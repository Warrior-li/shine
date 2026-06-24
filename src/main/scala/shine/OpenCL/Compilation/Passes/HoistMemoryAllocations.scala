package shine.OpenCL.Compilation.Passes

import arithexpr.arithmetic.ArithExpr.Math.Min
import rise.core.types.{AddressSpace, AddressSpaceIdentifier}
import rise.core.DSL.Type._
import shine.DPIA.DSL._
import shine.DPIA.primitives.imperative._
import shine.DPIA.Phrases.{VisitAndRebuild, _}
import shine.DPIA.Types._
import shine.DPIA._
import shine.OpenCL.primitives.imperative.{New, ParFor, ParForNat}
import shine._

object HoistMemoryAllocations {

  case class AllocationInfo(addressSpace: AddressSpace,
                            identifier: Identifier[VarType])

  def hoist: Phrase[CommType] => (scala.Seq[AllocationInfo], Phrase[CommType]) = originalPhrase => {
    val visitor = new VisitorScope(List[AllocationInfo]()).Visitor(List())

    val rewrittenPhrase = VisitAndRebuild(originalPhrase, visitor)

    (normalizeAllocations(visitor.getReplacedAllocations), rewrittenPhrase)
    //    // Create a fresh allocation for every replaced New node using initially the
    //    // rewrittenPhrase and then the previous New node as its nested body
    //    replacedAllocations.foldLeft(rewrittenPhrase)((prev, alloc) => {
    //      val (addressSpace, identifier) = alloc
    //      New(identifier.t.t1.dataType, addressSpace, LambdaPhrase(identifier, prev))
    //    })
  }

  private def normalizeAllocations(
      allocations: scala.Seq[AllocationInfo]
  ): scala.Seq[AllocationInfo] = {
    allocations.foldRight(Vector.empty[AllocationInfo]) { (alloc, normalized) =>
      normalized.indexWhere(_.identifier.name == alloc.identifier.name) match {
        case -1 =>
          alloc +: normalized

        case idx =>
          val existing = normalized(idx)
          if (
            existing.addressSpace != alloc.addressSpace ||
              existing.identifier.t.t1.dataType != alloc.identifier.t.t1.dataType
          ) {
            throw new Exception(
              "conflicting hoisted memory allocations for " +
                s"'${alloc.identifier.name}': " +
                s"${existing.addressSpace} ${existing.identifier.t.t1.dataType} vs " +
                s"${alloc.addressSpace} ${alloc.identifier.t.t1.dataType}"
            )
          }
          normalized
      }
    }
  }

  private class VisitorScope(var replacedAllocations: List[AllocationInfo]) {

    case class ParForInfo(parallelismLevel: shine.OpenCL.ParallelismLevel,
                          allocations: Nat,
                          allocation: Either[Identifier[ExpType], Nat])

    case class Visitor(parForInfos: List[ParForInfo]) extends VisitAndRebuild.Visitor {

      def getReplacedAllocations: scala.Seq[AllocationInfo] = replacedAllocations

      override def phrase[T <: PhraseType](p: Phrase[T]): Result[Phrase[T]] = {
        p match {
          // 1 thread only needs 1 allocation
          // `t` threads need `t` individual allocations
          // we also do not need more allocations that loop iterations
          case f: For => Continue(f,
            Visitor(ParForInfo(OpenCL.Sequential, Min(1, f.n), Right(0)) :: parForInfos))
          case f: ForNat => Continue(f,
            Visitor(ParForInfo(OpenCL.Sequential, Min(1, f.n), Right(0)) :: parForInfos))
          case pf: ParFor =>
            Continue(pf,
              Visitor(ParForInfo(pf.level, Min(pf.step, pf.n), Right(pf.init)) :: parForInfos))
          case pf: ParForNat =>
            Continue(pf,
              Visitor(ParForInfo(pf.level, Min(pf.step, pf.n), Right(pf.init)) :: parForInfos))

          case New(addressSpace, _, Lambda(variable, body)) if addressSpace != AddressSpace.Private =>
            Stop( // TODO? there might be fors and news in the body
              replaceNew(addressSpace.asInstanceOf[AddressSpace],
                variable, body)).asInstanceOf[Result[Phrase[T]]]

          case _ => Continue(p, this)
        }
      }

      private def replaceNew(addressSpace: AddressSpace,
                             variable: Identifier[VarType],
                             body: Phrase[CommType]): Phrase[CommType] = {
        // Replace `new` node by looking through the information from the `par for`s.
        //
        // Global memory can be hoisted across all surrounding parallel loops by
        // adding one allocation dimension for each loop.
        //
        // Local memory has OpenCL work-group scope. It can be hoisted through
        // local/sequential loops, but it must stop at the nearest work-group
        // boundary. Hoisting it further outside a global loop would lose the
        // per-work-group ownership of `__local` memory.
        val (finalVariable, finalBody) = addressSpace match {
          case AddressSpace.Global =>
            parForInfos.foldLeft((variable, body)) {
              case ((oldVariable, oldBody), ParForInfo(_, n, i)) =>
                performRewrite(oldVariable, oldBody, i, n)
            }

          case AddressSpace.Local =>
            hoistLocalUntilWorkGroup(variable, body, parForInfos)

          case AddressSpace.Private | AddressSpace.Constant | AddressSpaceIdentifier(_) =>
            throw new Exception("This can't happen")
        }

        // ... remember `finalVariable' to regenerate the `new' at the
        // outermost scope and return the rewritten finalBody which
        // replaces the old `new` node
        replacedAllocations = AllocationInfo(addressSpace, finalVariable) :: replacedAllocations
        VisitAndRebuild(finalBody, this)
      }

      private def hoistLocalUntilWorkGroup(
          variable: Identifier[VarType],
          body: Phrase[CommType],
          infos: List[ParForInfo]
      ): (Identifier[VarType], Phrase[CommType]) = {
        infos.foldLeft((variable, body, false)) {
          case ((oldVariable, oldBody, true), _) =>
            (oldVariable, oldBody, true)

          case ((oldVariable, oldBody, false), ParForInfo(parallelismLevel, n, i)) =>
            parallelismLevel match {
              case OpenCL.Local | OpenCL.Sequential =>
                val (newVariable, newBody) = performRewrite(oldVariable, oldBody, i, n)
                (newVariable, newBody, false)

              case OpenCL.WorkGroup =>
                (oldVariable, oldBody, true)

              case OpenCL.Global =>
                throw new Exception(
                  "local memory allocation must be inside an explicit work-group scope; " +
                    "place toLocal under mapWorkGroup/mapLocal or use global/private memory")

              case OpenCL.Warp | OpenCL.Lane =>
                throw new Exception("This should not happen")
            }
        } match {
          case (finalVariable, finalBody, _) => (finalVariable, finalBody)
        }
      }

      private def performRewrite(oldVariable: Identifier[VarType],
                                 oldBody: Phrase[CommType],
                                 i: Either[Identifier[ExpType], Nat],
                                 n: Nat): (Identifier[VarType], Phrase[CommType]) = {
        // Create `newVariable' with `n` times more memory ...
        val newVariable = Identifier(oldVariable.name, varT(n `.` oldVariable.t.t1.dataType))
        // ... and substitute all occurrences of `oldVariable` with
        // `newVariable` indexed by the index `i`, ...
        val newBody = i match {
          case Left(identExpr) =>
            Phrase.substitute(
              substitutionMap = Map(
                oldVariable.rd -> (newVariable.rd `@` identExpr),
                oldVariable.wr -> (newVariable.wr `@` identExpr)
              ),
              in = oldBody
            )
          case Right(identNat) =>
            Phrase.substitute(
              substitutionMap = Map(
                oldVariable.rd -> (newVariable.rd `@` identNat),
                oldVariable.wr -> (newVariable.wr `@` identNat)
              ),
              in = oldBody
            )
        }
        // ... finally, return `newParam' and `newBody'.
        (newVariable, newBody)
      }
    }

  }

}
