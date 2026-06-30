package shine.OpenCL.Compilation.Passes

import rise.core.types.{AddressSpace, NatKind}
import shine.DPIA.{->:, NatIdentifier}
import shine.DPIA.Phrases._
import shine.DPIA.Types._
import shine.DPIA.primitives.functional
import shine.DPIA.primitives.functional.{Map => _, _}
import shine.DPIA.primitives.imperative._
import shine.OpenCL
import shine.OpenCL.Compilation.Passes.HoistMemoryAllocations.AllocationInfo
import shine.OpenCL.Local
import shine.OpenCL.primitives.{imperative => ocl}

/**
 * Insert barriers for local buffers that were hoisted out of lexical `new`
 * nodes and became kernel local parameters.
 *
 * The regular InsertMemoryBarriers pass runs before HoistMemoryAllocations and
 * therefore cannot see those post-hoist local parameters as allocations. This
 * pass is intentionally narrow: it only tracks hoisted AddressSpace.Local
 * allocations and only inserts local fences for write->read or read->write
 * dependencies on the same allocation name.
 */
object InsertHoistedLocalMemoryBarriers {
  def insert:
      ((scala.Seq[AllocationInfo], Phrase[CommType])) => (scala.Seq[AllocationInfo], Phrase[CommType]) = {
    case (allocations, phrase) =>
      val localNames = allocations
        .filter(_.addressSpace == AddressSpace.Local)
        .map(_.identifier.name)
        .toSet

      if (localNames.isEmpty) {
        (allocations, phrase)
      } else {
        (allocations, transformCommand(phrase, localNames)._1)
      }
  }

  private case class Effects(reads: Set[String] = Set.empty, writes: Set[String] = Set.empty) {
    def ++(other: Effects): Effects =
      Effects(reads ++ other.reads, writes ++ other.writes)

    def needsBarrierBefore(next: Effects): Boolean =
      writes.exists(next.reads.contains) || reads.exists(next.writes.contains)

    def hasLocalReuse: Boolean =
      reads.intersect(writes).nonEmpty

    def touchesLocal: Boolean =
      reads.nonEmpty || writes.nonEmpty
  }

  private def localBarrier: Phrase[CommType] =
    OpenCL.DSL.barrier(local = true, global = false)

  private def isLocalBarrier(p: Phrase[CommType]): Boolean =
    p match {
      case ocl.Barrier(true, false) => true
      case _ => false
    }

  private def sequence(a: Phrase[CommType], b: Phrase[CommType]): Phrase[CommType] =
    (a, b) match {
      case (left, right) if isLocalBarrier(left) && isLocalBarrier(right) =>
        left
      case (Seq(prefix, left), right) if isLocalBarrier(left) && isLocalBarrier(right) =>
        Seq(prefix, left)
      case (left, Seq(right, suffix)) if isLocalBarrier(left) && isLocalBarrier(right) =>
        Seq(left, suffix)
      case _ =>
        Seq(a, b)
    }

  private def withLoopCarriedBarrier(body: Phrase[CommType], effects: Effects): Phrase[CommType] =
    if (effects.hasLocalReuse) {
      sequence(body, localBarrier)
    } else {
      body
    }

  private def transformCommand(
      p: Phrase[CommType],
      localNames: Set[String]
  ): (Phrase[CommType], Effects) = {
    p match {
      case Seq(a, b) =>
        val (a2, ae) = transformCommand(a, localNames)
        val (b2, be) = transformCommand(b, localNames)
        val joined =
          if (ae.needsBarrierBefore(be)) {
            sequence(a2, sequence(localBarrier, b2))
          } else {
            sequence(a2, b2)
          }
        (joined, ae ++ be)

      case f@For(unroll) =>
        f.loopBody match {
          case Lambda(x, body) =>
            val (body2, effects) = transformCommand(body, localNames)
            val guardedBody = withLoopCarriedBarrier(body2, effects)
            val rebuilt = For(unroll)(f.n, Lambda(x, guardedBody))
            (rebuilt, effects)
          case _ => throw new Exception("This should not happen")
        }

      case f@ForNat(unroll) =>
        f.loopBody match {
          case DepLambda(NatKind, x, body) =>
            val (body2, effects) = transformCommand(body, localNames)
            val guardedBody = withLoopCarriedBarrier(body2, effects)
            val rebuilt = ForNat(unroll)(f.n, DepLambda(NatKind, x, guardedBody))
            (rebuilt, effects)
          case _ => throw new Exception("This should not happen")
        }

      case fv@ForVec(_, _, _, _) =>
        fv.loopBody match {
          case Lambda(x, Lambda(o, body)) =>
            val (body2, effects) = transformCommand(body, localNames)
            val guardedBody = withLoopCarriedBarrier(body2, effects)
            val rebuilt = ForVec(fv.n, fv.dt, fv.out, Lambda(x, Lambda(o, guardedBody)))
            (rebuilt, effects)
          case _ => throw new Exception("This should not happen")
        }

      case n@New(_, _) =>
        n.f match {
          case Lambda(x, body) =>
            val (body2, effects) = transformCommand(body, localNames)
            val rebuilt = New(n.dt, Lambda(x, body2))
            (rebuilt, effects)
          case _ => throw new Exception("This should not happen")
        }

      case n@ocl.New(_, _, _) =>
        n.f match {
          case Lambda(x, body) =>
            val (body2, effects) = transformCommand(body, localNames)
            val rebuilt = ocl.New(n.a, n.dt, Lambda(x, body2))
            (rebuilt, effects)
          case _ => throw new Exception("This should not happen")
        }

      case pf@ocl.ParFor(level, dim, unroll, name) =>
        pf.body match {
          case Lambda(x, Lambda(o, body)) =>
            val (body2, bodyEffects) = transformCommand(body, localNames)
            val outputEffects =
              if (level == Local) Effects(writes = collectWrites(pf.out, localNames)) else Effects()
            val effects = bodyEffects ++ outputEffects
            val rebuilt = ocl.ParFor(level, dim, unroll, name)(pf.init, pf.n, pf.step, pf.dt, pf.out,
              Lambda(x, Lambda(o, body2)))
            (rebuilt, effects)
          case _ => throw new Exception("This should not happen")
        }

      case pf@ocl.ParForNat(level, dim, unroll, name) =>
        pf.body match {
          case DepLambda(NatKind, i: NatIdentifier, Lambda(o, body)) =>
            val (body2, bodyEffects) = transformCommand(body, localNames)
            val outputEffects =
              if (level == Local) Effects(writes = collectWrites(pf.out, localNames)) else Effects()
            val effects = bodyEffects ++ outputEffects
            val rebuilt = ocl.ParForNat(level, dim, unroll, name)(pf.init, pf.n, pf.step, pf.ft, pf.out,
              DepLambda(NatKind, i, Lambda(o, body2)))
            (rebuilt, effects)
          case _ => throw new Exception("This should not happen")
        }

      case Assign(_, lhs, rhs) =>
        val effects = Effects(
          reads = collectReads(rhs, localNames),
          writes = collectWrites(lhs, localNames)
        )
        (p, effects)

      case Skip() | Comment(_) | ocl.Barrier(_, _) =>
        (p, Effects())

      case _ =>
        (p, Effects(reads = localNames, writes = localNames))
    }
  }

  private def collectWrites(a: Phrase[AccType], localNames: Set[String]): Set[String] = {
    def fromIdent(i: Identifier[_ <: PhraseType]): Set[String] =
      if (localNames.contains(i.name)) Set(i.name) else Set.empty

    a match {
      case i: Identifier[_] => fromIdent(i)
      case Proj1(p) => collectRootNames(p, localNames)
      case Proj2(p) => collectRootNames(p, localNames)
      case IdxAcc(_, _, _, a) => collectWrites(a, localNames)
      case MapAcc(_, _, _, _, a) => collectWrites(a, localNames)
      case JoinAcc(_, _, _, a) => collectWrites(a, localNames)
      case SplitAcc(_, _, _, a) => collectWrites(a, localNames)
      case AsScalarAcc(_, _, _, a) => collectWrites(a, localNames)
      case idx: ocl.IdxDistributeAcc => collectWrites(idx.array, localNames)
      case PairAcc1(_, _, a) => collectWrites(a, localNames)
      case PairAcc2(_, _, a) => collectWrites(a, localNames)
      case PairAcc(_, _, a, b) => collectWrites(a, localNames) ++ collectWrites(b, localNames)
      case TakeAcc(_, _, _, a) => collectWrites(a, localNames)
      case PadEmptyAcc(_, _, _, a) => collectWrites(a, localNames)
      case TransposeAcc(_, _, _, a) => collectWrites(a, localNames)
      case ScatterAcc(_, _, _, _, a) => collectWrites(a, localNames)
      case UnzipAcc(_, _, _, a) => collectWrites(a, localNames)
      case _ => Set.empty
    }
  }

  private def collectReads(e: Phrase[ExpType], localNames: Set[String]): Set[String] = {
    def allLocal(): Set[String] = localNames

    e match {
      case i: Identifier[_] => collectRootNames(i, localNames)
      case Proj1(p) => collectRootNames(p, localNames)
      case Proj2(p) => collectRootNames(p, localNames)
      case _: Literal => Set.empty
      case Natural(_) => Set.empty
      case UnaryOp(_, e) => collectReads(e, localNames)
      case BinOp(_, e1, e2) => collectReads(e1, localNames) ++ collectReads(e2, localNames)
      case IfThenElse(cond, thenP, elseP) =>
        collectReads(cond, localNames) ++ collectReads(thenP, localNames) ++ collectReads(elseP, localNames)
      case Idx(_, _, e1, e2) => collectReads(e1, localNames) ++ collectReads(e2, localNames)
      case Slide(_, _, _, _, e) => collectReads(e, localNames)
      case functional.Map(_, _, _, _, _, e) => collectReads(e, localNames)
      case idx: ocl.IdxDistribute => collectReads(idx.array, localNames)
      case MapRead(_, _, _, _, e) => collectReads(e, localNames)
      case GenerateCont(_, _, _) => allLocal()
      case AsScalar(_, _, _, _, e) => collectReads(e, localNames)
      case AsVectorAligned(_, _, _, _, e) => collectReads(e, localNames)
      case AsVector(_, _, _, _, e) => collectReads(e, localNames)
      case VectorFromScalar(_, _, e) => collectReads(e, localNames)
      case Fst(_, _, e) => collectReads(e, localNames)
      case Snd(_, _, e) => collectReads(e, localNames)
      case Transpose(_, _, _, _, e) => collectReads(e, localNames)
      case Join(_, _, _, _, e) => collectReads(e, localNames)
      case Split(_, _, _, _, e) => collectReads(e, localNames)
      case Zip(_, _, _, _, e1, e2) => collectReads(e1, localNames) ++ collectReads(e2, localNames)
      case PadCst(_, _, _, _, e1, e2) => collectReads(e1, localNames) ++ collectReads(e2, localNames)
      case PadClamp(_, _, _, _, e) => collectReads(e, localNames)
      case Cast(_, _, e) => collectReads(e, localNames)
      case ffc@ForeignFunctionCall(_, _) =>
        ffc.args.foldLeft(Set.empty[String])(_ ++ collectReads(_, localNames))
      case NatAsIndex(_, e) => collectReads(e, localNames)
      case IndexAsNat(_, e) => collectReads(e, localNames)
      case Drop(_, _, _, _, e) => collectReads(e, localNames)
      case Take(_, _, _, _, e) => collectReads(e, localNames)
      case Unzip(_, _, _, _, e) => collectReads(e, localNames)
      case MakePair(_, _, _, e1, e2) => collectReads(e1, localNames) ++ collectReads(e2, localNames)
      case Reorder(_, _, _, _, _, e) => collectReads(e, localNames)
      case m@MakeArray(_) =>
        m.elements.foldLeft(Set.empty[String])(_ ++ collectReads(_, localNames))
      case Gather(_, _, _, e1, e2) => collectReads(e1, localNames) ++ collectReads(e2, localNames)
      case _ => allLocal()
    }
  }

  @scala.annotation.tailrec
  private def collectRootNames(
      p: Phrase[_ <: PhraseType],
      localNames: Set[String]
  ): Set[String] = {
    p match {
      case i: Identifier[_] if localNames.contains(i.name) => Set(i.name)
      case _: Identifier[_] => Set.empty
      case Proj1(e) => collectRootNames(e, localNames)
      case Proj2(e) => collectRootNames(e, localNames)
      case _ => Set.empty
    }
  }
}
