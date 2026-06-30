package shine.DPIA.Compilation

import arithexpr.arithmetic.{Cst, NamedVar, RangeAdd}
import shine.DPIA.Compilation.TranslationToImperative._
import shine.DPIA.DSL.{comment, _}
import shine.DPIA.Phrases._
import rise.core.types.{AddressSpace, DataType, Fragment, MatrixLayout, NatIdentifier, NatKind, read, write}
import rise.core.DSL.Type._
import rise.core.types.DataType._
import rise.core.substitute.{natInType => substituteNatInType}
import shine.DPIA.Types.{AccType, CommType, ExpType, FunType, TypeCheck, comm}
import rise.core.types.DataTypeOps._
import shine.DPIA._
import shine.DPIA.primitives.functional._
import shine.DPIA.primitives.imperative.{Seq => _, _}
import shine.OpenCL.AdjustArraySizesForAllocations
import shine.OpenCL.get_local_id
import shine.OpenMP.primitives.{functional => omp}
import shine.OpenCL.primitives.{functional => ocl}
import shine.OpenCL.primitives.{imperative => oclImp}
import shine.cuda.primitives.{functional => cuda}
import shine.cuda.primitives.{imperative => cudaImp}

object AcceptorTranslation {
  private def readLeaves(dt: DataType, input: Phrase[ExpType]): Seq[Phrase[ExpType]] =
    dt match {
      case ArrayType(Cst(n), elemT) =>
        (0 until n.toInt).flatMap(i => readLeaves(elemT, input `@` Cst(i)))
      case PairType(dt1, dt2) =>
        readLeaves(dt1, Fst(dt1, dt2, input)) ++
          readLeaves(dt2, Snd(dt1, dt2, input))
      case _ =>
        Seq(input)
    }

  private def accLeaves(dt: DataType, output: Phrase[AccType]): Seq[Phrase[AccType]] =
    dt match {
      case ArrayType(Cst(n), elemT) =>
        (0 until n.toInt).flatMap(i => accLeaves(elemT, output `@` Cst(i)))
      case PairType(dt1, dt2) =>
        accLeaves(dt1, pairAcc1(dt1, dt2, output)) ++
          accLeaves(dt2, pairAcc2(dt1, dt2, output))
      case _ =>
        Seq(output)
    }

  def acc(E: Phrase[ExpType])
         (A: Phrase[AccType])
         (implicit context: TranslationContext): Phrase[CommType] = {
    def copyReadValueInto(
      dt: DataType,
      input: Phrase[ExpType],
      output: Phrase[AccType]
    ): Phrase[CommType] = dt match {
      case ArrayType(n, elemT) =>
        `for`(n, i => copyReadValueInto(elemT, input `@` i, output `@` i))
      case PairType(dt1, dt2) =>
        copyReadValueInto(dt1, Fst(dt1, dt2, input), pairAcc1(dt1, dt2, output)) `;`
          copyReadValueInto(dt2, Snd(dt1, dt2, input), pairAcc2(dt1, dt2, output))
      case _ =>
        output :=| dt | input
    }

    E match {
      // on the fly beta-reduction
      case Apply(fun, arg) => acc(Lifting.liftFunction(fun).reducing(arg))(A)
      case DepApply(kind, fun, arg) => arg match {
        case a: Nat =>
          acc(Lifting.liftDependentFunction(
            fun.asInstanceOf[ Phrase[`(nat)->:`[ExpType]]])(a))(A)
        case a: DataType =>
          acc(Lifting.liftDependentFunction(
            fun.asInstanceOf[Phrase[`(dt)->:`[ExpType]]])(a))(A)
      }

      case staticIterate@StaticIterate(_, _, _, _) =>
        primitive(staticIterate)(A)

      case grouped: ocl.GroupedReduceSeqInitAggregate =>
        primitive(grouped)(A)

      case grouped: ocl.GroupedReducePrivateSeqInitAggregate =>
        primitive(grouped)(A)

      case grouped: ocl.GroupedReduceSeqInitAggregateNested =>
        primitive(grouped)(A)

      case e
        if TypeCheck.notContainingArrayType(e.t.dataType)
          && e.t.accessType == read =>
        //FIXME
        // The pattern matching is needed in order to generate separate
        // assignments to elements of pairs (structs), because the AMD SDK
        // cannot deal with literal struct assignments or definitions (C99).
        e match {
          case MakePair(dt1, dt2, _, fst, snd) =>
            acc(fst)(pairAcc1(dt1, dt2, A)) `;`
              acc(snd)(pairAcc2(dt1, dt2, A))
          case _ =>
            con(e)(fun(e.t)(a => A :=| e.t.dataType | a))
        }

      case c: Literal => A :=|c.t.dataType| c

      case x: Identifier[ExpType] => copyReadValueInto(x.t.dataType, x, A)

      case n: Natural => A :=|n.t.dataType| n

      case u@UnaryOp(op, e) =>
        con(e)(fun(u.t)(x =>
          A :=|u.t.dataType| UnaryOp(op, x)
        ))

      case b@BinOp(op, e1, e2) =>
        con(e1)(fun(b.t)(x =>
          con(e2)(fun(b.t)(y =>
            A :=|b.t.dataType| BinOp(op, x, y)
          ))
        ))

      case ep: ExpPrimitive => primitive(ep)(A)

      case LetNat(binder, defn, body) => LetNat(binder, defn, acc(body)(A))

      case IfThenElse(cond, thenP, elseP) =>
        con(cond)(fun(cond.t) { x =>
          `if` (x) `then` acc(thenP)(A) `else` acc(elseP)(A)
        })

      case Proj1(_) => throw new Exception("This should never happen")
      case Proj2(_) => throw new Exception("This should never happen")
    }
  }

  def primitive(E: ExpPrimitive)
               (A: Phrase[AccType])
               (implicit context: TranslationContext): Phrase[CommType] = {
    def copyReadInto(
      dt: DataType,
      input: Phrase[ExpType],
      output: Phrase[AccType]
    ): Phrase[CommType] = {
      def destinationPassingReduceSeq(
        n: Nat,
        dt1: DataType,
        dt2: DataType,
        f: Phrase[FunType[ExpType, FunType[ExpType, ExpType]]],
        init: Phrase[ExpType],
        array: Phrase[ExpType],
        unroll: Boolean,
        output: Phrase[AccType]
      ): Phrase[CommType] =
        con(array)(fun(expT(n`.`dt1, read))(x =>
          comment("reduceSeq materialize") `;`
            `new`(dt2, accumulator =>
              copyReadInto(dt2, init, accumulator.wr) `;`
                `for`(unroll, n, i =>
                  copyReadInto(dt2, f(accumulator.rd)(x `@` i), accumulator.wr)) `;`
                copyReadInto(dt2, accumulator.rd, output))))

      def destinationPassingOclReduceSeq(
        n: Nat,
        addressSpace: AddressSpace,
        dt1: DataType,
        dt2: DataType,
        f: Phrase[FunType[ExpType, FunType[ExpType, ExpType]]],
        init: Phrase[ExpType],
        array: Phrase[ExpType],
        unroll: Boolean,
        output: Phrase[AccType]
      ): Phrase[CommType] =
        con(array)(fun(expT(n`.`dt1, read))(x => {
          val adj = AdjustArraySizesForAllocations(init, dt2, addressSpace)
          val needsLocalFence = addressSpace != AddressSpace.Private
          val beforeReduce =
            if (needsLocalFence) shine.OpenCL.DSL.barrier(local = true, global = false)
            else Skip()
          val afterReduce =
            if (needsLocalFence) shine.OpenCL.DSL.barrier(local = true, global = false)
            else Skip()

          comment("oclReduceSeq materialize") `;`
            beforeReduce `;`
            shine.OpenCL.DSL.`new`(addressSpace)(adj.dt, accumulator =>
              copyReadInto(dt2, init, adj.accF(accumulator.wr)) `;`
                `for`(unroll, n, i =>
                  copyReadInto(
                    dt2,
                    f(adj.exprF(accumulator.rd))(x `@` i),
                    adj.accF(accumulator.wr))) `;`
                copyReadInto(dt2, adj.exprF(accumulator.rd), output)) `;`
            afterReduce
        }))

      def destinationPassingStaticIterate(
        n: Nat,
        dt: DataType,
        f: Phrase[FunType[ExpType, FunType[ExpType, ExpType]]],
        init: Phrase[ExpType],
        output: Phrase[AccType]
      ): Phrase[CommType] =
        comment("staticIterate materialize") `;`
          shine.OpenCL.DSL.`new`(AddressSpace.Private)(dt, accumulator =>
            copyReadInto(dt, init, accumulator.wr) `;`
              `for`(n, i =>
                acc(f(i)(accumulator.rd))(accumulator.wr)) `;`
              copyReadInto(dt, accumulator.rd, output))

      input match {
        case Materialize(_, inner) =>
          copyReadInto(dt, inner, output)

        case Generate(n, elemT, f) =>
          dt match {
            case ArrayType(_, _) =>
              `for`(n, i => copyReadInto(elemT, f(i), output `@` i))
            case _ =>
              con(input)(fun(expT(dt, read))(x => output :=| dt | x))
          }

        case makeArray@MakeArray(n) =>
          val (elemT, elements) = makeArray.unwrap
          dt match {
            case ArrayType(_, _) if n == elements.length =>
              elements.zipWithIndex.foldLeft(
                comment("materialize MakeArray"): Phrase[CommType]) {
                case (body, (elem, idx)) =>
                  body `;` copyReadInto(
                    elemT,
                    elem,
                    output `@` Cst(idx))
              }
            case _ =>
              con(input)(fun(expT(dt, read))(x => output :=| dt | x))
          }

        case MakePair(dt1, dt2, _, fst, snd) =>
          copyReadInto(dt1, fst, pairAcc1(dt1, dt2, output)) `;`
            copyReadInto(dt2, snd, pairAcc2(dt1, dt2, output))

        case mapSeq@MapSeq(unroll) =>
          val (n, dt1, dt2, f, array) = mapSeq.unwrap
          con(array)(fun(expT(n`.`dt1, read))(x =>
            comment("mapSeq materialize") `;`
              `for`(unroll, n, i =>
                copyReadInto(dt2, f(x `@` i), output `@` i))))

        case reduceSeq@ReduceSeq(unroll) =>
          val (n, dt1, dt2, f, init, array) = reduceSeq.unwrap
          destinationPassingReduceSeq(n, dt1, dt2, f, init, array, unroll, output)

        case reduceSeq@ocl.ReduceSeq(unroll) =>
          val (n, addressSpace, dt1, dt2, f, init, array) = reduceSeq.unwrap
          destinationPassingOclReduceSeq(
            n, addressSpace, dt1, dt2, f, init, array, unroll, output)

        case staticIterate@StaticIterate(_, _, _, _) =>
          val (n, dt, f, init) = staticIterate.unwrap
          destinationPassingStaticIterate(n, dt, f, init, output)

        case LocalOwner(_, inner) =>
          `if`(localOwnerCondition) `then` copyReadInto(dt, inner, output) `else` Skip()

        case _ =>
          dt match {
            case ArrayType(n, elemT) =>
              con(input)(fun(expT(n`.`elemT, read))(x =>
                `for`(n, i => copyReadInto(elemT, x `@` i, output `@` i))
              ))
            case PairType(dt1, dt2) =>
              con(input)(fun(expT(dt1 x dt2, read))(x =>
                copyReadInto(dt1, Fst(dt1, dt2, x), pairAcc1(dt1, dt2, output)) `;`
                  copyReadInto(dt2, Snd(dt1, dt2, x), pairAcc2(dt1, dt2, output))
              ))
            case _ =>
              con(input)(fun(expT(dt, read))(x =>
                output :=| dt | x))
          }
      }
    }

    E match {
    case makeArray@MakeArray(n) =>
      val (elemT, elements) = makeArray.unwrap
      elements.zipWithIndex.foldLeft(
        comment("makeArray"): Phrase[CommType]) {
        case (body, (elem, idx)) =>
          body `;` acc(elem)(A `@` Cst(idx))
      }

    case Generate(n, _, f) =>
      `for`(n, i => acc(f(i))(A `@` i))

    case AsScalar(n, m, dt, access, array) =>
      acc(array)(AsScalarAcc(n, m, dt, A))

    case AsVector(n, m, dt, access, array) =>
      acc(array)(AsVectorAcc(n, m, dt, A))

    case AsVectorAligned(n, m, dt, access, array) =>
      acc(array)(AsVectorAcc(n, m, dt, A))

    case DepIdx(n, ft, index, array) =>
      con(array)(fun(expT(n`.d`ft, read))(x =>
        A :=| ft(index) | DepIdx(n, ft, index, x)))

    case DepJoin(n, lenF, dt, array) =>
      acc(array)(DepJoinAcc(n, lenF, dt, A))

    case depMapSeq@DepMapSeq(unroll) =>
      val (n, ft1, ft2, f, array) = depMapSeq.unwrap
      con(array)(fun(expT(n`.d`ft1, read))(x =>
        forNat(unroll, n, i =>
          acc(f(i)(x `@d` i))(A `@d` i))
      ))

    case DepTile(n, tileSize, haloSize, dt1, dt2, processTiles, array) =>
      ???

    case DMatch(x, elemT, outT, a, f, input) =>
      // Turn the f imperative by means of forwarding the acceptor translation
      con(input)(fun(expT(DepPairType(NatKind, x, elemT), read))(pair =>
        DMatchI(x, elemT, outT,
          depFun(NatKind)((fst: NatIdentifier) =>
            fun(expT(substituteNatInType(fst, x, elemT), read))(snd =>
              acc(f(fst)(snd))(A)
            )), pair)))

    case IdxVec(n, st, index, vector) =>
      con(vector)(fun(expT(vec(n, st), read))(x =>
        A :=| st | IdxVec(n, st, index, x)))

    case Iterate(n, m, k, dt, f, array) =>
      con(array)(fun(expT((m * n.pow(k))`.`dt, read))(x => {
        val sz = n.pow(k) * m

        newDoubleBuffer(sz`.`dt, m`.`dt, sz`.`dt, x, A,
          (v: Phrase[VarType],
           swap: Phrase[CommType],
           done: Phrase[CommType]) => {
            `for`(k, ip => {
              val i = NamedVar(ip.name)

              val isz = n.pow(k - i) * m
              val osz = n.pow(k - i - 1) * m
              acc(f(osz)(Take(isz, sz - isz, dt, read, v.rd)))(TakeAcc(osz, sz - osz, dt, v.wr)) `;`
                IfThenElse(ip < NatAsIndex(k, Natural(k - 2)), swap, done)
            })
          })
      }))

    case IterateStream(n, dt1, dt2, f, array) =>
      val fI = fun(expT(dt1, read))(x => fun(accT(dt2))(o => acc(f(x))(o)))
      val i = NatIdentifier(freshName("i"))
      str(array)(fun((i: NatIdentifier) ->:
        (expT(dt1, read) ->: (comm: CommType)) ->: (comm: CommType)
      )(next =>
        comment("iterateStream") `;`
          forNat(n, i =>
            streamNext(next, i, fun(expT(dt1, read))(x => fI(x)(A `@` i))))
      ))

    case staticIterate@StaticIterate(_, _, _, _) =>
      val (n, dt, f, init) = staticIterate.unwrap
      comment("staticIterate") `;`
        shine.OpenCL.DSL.`new`(AddressSpace.Private)(dt, accumulator =>
          copyReadInto(dt, init, accumulator.wr) `;`
            `for`(n, i =>
              acc(f(i)(accumulator.rd))(accumulator.wr)) `;`
            copyReadInto(dt, accumulator.rd, A))

    case Join(n, m, w, dt, array) =>
      acc(array)(JoinAcc(n, m, dt, A))

    case Take(n, m, dt, access, array) =>
      def copyPrefix(input: Phrase[ExpType]): Phrase[CommType] =
        `for`(n, i =>
          copyReadInto(
            dt,
            input `@` NatAsIndex(n + m, IndexAsNat(n, i)),
            A `@` i))

      access match {
        case `write` =>
          acc(array)(PadEmptyAcc(n, m, dt, A))
        case _ =>
          con(array)(fun(expT((n + m)`.`dt, read))(copyPrefix))
      }

    case Drop(n, m, dt, access, array) =>
      def copySuffix(input: Phrase[ExpType]): Phrase[CommType] =
        `for`(m, i =>
          copyReadInto(
            dt,
            input `@` NatAsIndex(n + m, IndexAsNat(m, i) + Natural(n)),
            A `@` i))

      access match {
        case `write` =>
          shine.OpenCL.DSL.`new`(AddressSpace.Private)((n + m)`.`dt, tmp =>
            acc(array)(tmp.wr) `;` copySuffix(tmp.rd))
        case _ =>
          con(array)(fun(expT((n + m)`.`dt, read))(copySuffix))
      }

    case Let(dt1, dt2, access, value, f) =>
      con(value)(fun(value.t)(x =>
        acc(f(x))(A)))

    case Materialize(dt, input) =>
      comment("materialize") `;` copyReadInto(dt, input, A)

    case LocalOwner(_, input) =>
      `if`(localOwnerCondition) `then` acc(input)(A) `else` Skip()

    case MakeDepPair(a, fst, sndT, snd) =>
      // We have the acceptor already, so simply write the first element and then
      // the second element in sequentially
      MkDPairFstI(fst, A) `;`
        acc(snd)(MkDPairSndAcc(fst, sndT, A))

    case MakePair(dt1, dt2, access, fst, snd) =>
      acc(fst)(pairAcc1(dt1, dt2, A)) `;`
        acc(snd)(pairAcc2(dt1, dt2, A))

    case Map(n, dt1, dt2, access, f, array) =>
      con(array)(fun(expT(n`.`dt1, read))(x =>
        `for`(n, i => copyReadInto(dt2, f(x `@` i), A `@` i))
      ))

    case MapFst(w, dt1, dt2, dt3, f, record) =>
      val x = Identifier(freshName("fede_x"), ExpType(dt1, write))

      val otype = AccType(dt3)
      val o = Identifier(freshName("fede_o"), otype)

      acc(record)(MapFstAcc(dt1, dt2, dt3,
        Lambda(o, fedAcc(scala.Predef.Map(x -> o))(f(x))(fun(otype)(x => x))),
        A))

    case mapSeq@MapSeq(unroll) =>
      val (n, dt1, dt2, f, array) = mapSeq.unwrap
      con(array)(fun(expT(n`.`dt1, read))(x =>
        comment("mapSeq")`;`
          `for`(unroll, n, i => acc(f(x `@` i))(A `@` i))
      ))

    case MapSnd(w, dt1, dt2, dt3, f, record) =>
      val x = Identifier(freshName("fede_x"), ExpType(dt2, write))

      val otype = AccType(dt3)
      val o = Identifier(freshName("fede_o"), otype)

      acc(record)(MapSndAcc(dt1, dt2, dt3,
        Lambda(o, fedAcc(scala.Predef.Map(x -> o))(f(x))(fun(otype)(x => x))),
        A))

    case MapVec(n, dt1, dt2, f, array) =>
      con(array)(fun(expT(vec(n, dt1), read))(x =>
        shine.OpenMP.DSL.parForVec(n, dt2, A, i => a => acc(f(x `@v` i))(a))
      ))

    case PadEmpty(n, r, dt, array) =>
      acc(array)(TakeAcc(n, r, dt, A))

    case PrintType(msg, dt, access, input) =>
      acc(input)(A)

    case reduceSeq@ReduceSeq(unroll) =>
      val (n, dt1, dt2, f, init, array) = reduceSeq.unwrap
      copyReadInto(dt2, reduceSeq, A)

    case Reorder(n, dt, access, idxF, idxFinv, input) =>
      acc(input)(ReorderAcc(n, dt, idxFinv, A))

    case ScanSeq(n, dt1, dt2, f, init, array) =>
      con(array)(fun(expT(n`.`dt1, read))(x =>
        con(init)(fun(expT(dt2, read))(y =>
          comment("scanSeq")`;`
          `new`(dt2, accumulator =>
            acc(y)(accumulator.wr) `;`
            `for`(n, i =>
              acc(f(x `@` i)(accumulator.rd))(accumulator.wr) `;`
              //FIXME remove general assignment
              ((A `@` i) :=| dt2 | accumulator.rd) ))))))

    case Scatter(n, m, dt, indices, input) =>
      con(indices)(fun(expT(n`.`idx(m), read))(y =>
        acc(input)(ScatterAcc(n, m, dt, y, A))))

    case ProjectWrite(n, m, dt, _, indices, input) =>
      con(indices)(fun(expT(n`.`idx(m), read))(y =>
        acc(input)(ScatterAcc(n, m, dt, y, A))))

    case slide@Slide(n, sz, sp, dt, input) =>
      con(slide)(fun(expT(n`.`(sz`.`dt), read))(x =>
        A :=|(n`.`(sz`.`dt))| x ))

    case Split(n, m, w, dt, array) =>
      acc(array)(SplitAcc(n, m, dt, A))

    case Transpose(n, m, dt, access, array) =>
      acc(array)(TransposeAcc(n, m, dt, A))

    case Unzip(n, dt1, dt2, access, e) =>
      acc(e)(UnzipAcc(n, dt1, dt2, A))

    case VectorFromScalar(n, dt, arg) =>
      con(arg)(fun(expT(dt, read))(e =>
        A :=|vec(n, dt)| VectorFromScalar(n, dt, e)))

    case Zip(n, dt1, dt2, access, e1, e2) =>
      acc(e1)(ZipAcc1(n, dt1, dt2, A)) `;`
        acc(e2)(ZipAcc2(n, dt1, dt2, A))

    // OpenMP
    case omp.DepMapPar(n, ft1, ft2, f, array) =>
      con(array)(fun(expT(n`.d`ft1, read))(x => {
        shine.OpenMP.DSL.parForNat(n, ft2, A, idx => a => acc(f(idx)(x `@d` idx))(a))
      }))

    case omp.MapPar(n, dt1, dt2, f, array) =>
      con(array)(fun(expT(n`.`dt1, read))(x =>
        shine.OpenMP.DSL.parFor(n, dt2, A, i => a => acc(f(x `@` i))(a))))

    case reducePar@omp.ReducePar(n, dt1, dt2, f, init, array) =>
      con(reducePar)(fun(expT(dt2, write))(r =>
        acc(r)(A)))

    // OpenCL
    case depMap@ocl.DepMap(level, dim) =>
      val (n, ft1, ft2, f, array) = depMap.unwrap
      con(array)(fun(expT(n`.d`ft1, read))(x => {
        import shine.OpenCL.DSL._
        level match {
          case shine.OpenCL.Global =>
            parForNatGlobal(dim)(n, ft2, A, idx => a => acc(f(idx)(x `@d` idx))(a))
          case shine.OpenCL.Local =>
            parForNatLocal(dim)(n, ft2, A, idx => a => acc(f(idx)(x `@d` idx))(a)) `;` barrier()
          case shine.OpenCL.WorkGroup =>
            parForNatWorkGroup(dim)(n, ft2, A, idx => a => acc(f(idx)(x `@d` idx))(a))
          case shine.OpenCL.Sequential | shine.OpenCL.Warp | shine.OpenCL.Lane =>
            throw new Exception("This should not happen")
        }}))

    case ocl.Iterate(a, n, m, k, dt, f, array) =>
      con(array)(fun(expT({m * n.pow(k)}`.`dt, read))(x => {
        import arithexpr.arithmetic.Cst
        val sz = n.pow(k) * m

        shine.OpenCL.DSL.newDoubleBuffer(a, sz`.`dt, m`.`dt, sz`.`dt, x, A,
          (v, swap, done) => {
            shine.DPIA.DSL.`for`(k, ip => {
              val i = NamedVar(ip.name, RangeAdd(Cst(0), k, Cst(1)))

              val isz = n.pow(k - i) * m
              val osz = n.pow(k - i - 1) * m
              acc(f(osz)(Take(isz, sz - isz, dt, read, v.rd)))(TakeAcc(osz, sz - osz, dt, v.wr)) `;`
                IfThenElse(ip < NatAsIndex(k, Natural(k - 2)), swap, done)
            })
          })
      }))

    case ocl.GroupedReduceSeq(a, n, m, dt, f, input) =>
      if (a != AddressSpace.Local) {
        throw new Exception("oclGroupedReduceSeq currently lowers local reductions only")
      }
      val lanes = n match {
        case Cst(value) => BigInt(value)
        case _ => throw new Exception("oclGroupedReduceSeq needs a static lane count")
      }
      if (lanes <= 0 || (lanes & (lanes - 1)) != 0) {
        throw new Exception("oclGroupedReduceSeq needs a power-of-two lane count")
      }
      con(input)(fun(expT((m * n)`.`dt, read))(x => {
        val total = m * n

        def directCopy(): Phrase[CommType] =
          `for`(m, group =>
            copyReadInto(
              dt,
              x `@` NatAsIndex(total, IndexAsNat(m, group) * Natural(n)),
              A `@` group))

        val firstFanIn =
          if (lanes >= 8) BigInt(8)
          else if (lanes >= 4) BigInt(4)
          else BigInt(2)
        val firstStride = lanes / firstFanIn
        val scratchLanes = Natural(Cst(firstStride.toLong))
        val scratchTotal = m * Cst(firstStride.toLong)

        def copyFirstStageInto(
            leaves: Seq[Phrase[ExpType]],
            dst: Phrase[AccType]
        ): Phrase[CommType] = {
          leaves match {
            case Seq(one) =>
              copyReadInto(dt, one, dst)
            case Seq(lhs, rhs) =>
              copyReadInto(dt, f(lhs)(rhs), dst)
            case _ =>
              val (lhsLeaves, rhsLeaves) = leaves.splitAt(leaves.size / 2)
              shine.OpenCL.DSL.`new`(AddressSpace.Private)(dt, lhs =>
                shine.OpenCL.DSL.`new`(AddressSpace.Private)(dt, rhs =>
                  copyFirstStageInto(lhsLeaves, lhs.wr) `;`
                    copyFirstStageInto(rhsLeaves, rhs.wr) `;`
                    copyReadInto(dt, f(lhs.rd)(rhs.rd), dst)))
          }
        }

        def firstStage(scratch: Phrase[VarType]): Phrase[CommType] =
          shine.OpenCL.DSL.parFor(shine.OpenCL.Local, 0, unroll = false)(
            scratchTotal,
            dt,
            scratch.wr,
            fun(expT(idx(scratchTotal), read))(q => fun(accT(dt))(dst => {
              val qNat = IndexAsNat(scratchTotal, q)
              val groupNat = qNat / scratchLanes
              val laneNat = qNat % scratchLanes
              val srcNat = (groupNat * Natural(n)) + (laneNat * Natural(Cst(firstFanIn.toLong)))
              def src(offset: BigInt): Phrase[ExpType] =
                x `@` NatAsIndex(total, srcNat + Natural(Cst(offset.toLong)))
              copyFirstStageInto((0 until firstFanIn.toInt).map(i => src(BigInt(i))), dst)
            }))
          ) `;` shine.OpenCL.DSL.barrier(local = true, global = false)

        def stage(stride: BigInt)(scratch: Phrase[VarType]): Phrase[CommType] = {
          val strideArith = Cst(stride.toLong)
          val strideNat = Natural(strideArith)
          val workItems = m * strideArith
          shine.OpenCL.DSL.parFor(shine.OpenCL.Local, 0, unroll = false)(
            workItems,
            dt,
            TakeAcc(workItems, scratchTotal - workItems, dt, scratch.wr),
            fun(expT(idx(workItems), read))(q => fun(accT(dt))(_ => {
              val qNat = IndexAsNat(workItems, q)
              val groupNat = qNat / strideNat
              val laneNat = qNat % strideNat
              val groupBase = groupNat * scratchLanes
              val dst = NatAsIndex(scratchTotal, groupBase + laneNat)
              val srcNat = groupBase + (laneNat * Natural(2))
              val src0 = NatAsIndex(scratchTotal, srcNat)
              val src1 = NatAsIndex(scratchTotal, srcNat + Natural(1))
              copyReadInto(dt, f(scratch.rd `@` src0)(scratch.rd `@` src1), scratch.wr `@` dst)
            }))
          ) `;` shine.OpenCL.DSL.barrier(local = true, global = false)
        }

        val strides = Iterator.iterate(firstStride / 2)(_ / 2).takeWhile(_ >= 2).toSeq
        comment("oclGroupedReduceSeq") `;` (
          if (lanes == 1) {
            directCopy()
          } else {
            def root(scratch: Phrase[VarType], group: Phrase[ExpType]): Phrase[ExpType] = {
              val groupBase = IndexAsNat(m, group) * scratchLanes
              val lhs = scratch.rd `@` NatAsIndex(scratchTotal, groupBase)
              if (firstStride == 1) {
                lhs
              } else {
                f(lhs)(scratch.rd `@` NatAsIndex(scratchTotal, groupBase + Natural(1)))
              }
            }
            shine.OpenCL.DSL.`new`(AddressSpace.Local)(scratchTotal`.`dt, scratch =>
              firstStage(scratch) `;`
                strides.foldLeft(Skip(): Phrase[CommType])((body, stride) =>
                  body `;` stage(stride)(scratch)) `;`
                `for`(m, group =>
                  copyReadInto(dt, root(scratch, group), A `@` group)))
          })
      }))

    case ocl.GroupedReduceSeqInitAggregate(a, n, m, dt, outDt, f, init, input) =>
      if (a != AddressSpace.Local) {
        throw new Exception("oclGroupedReduceSeqInitAggregate currently lowers local reductions only")
      }
      val lanes = n match {
        case Cst(value) => BigInt(value)
        case _ => throw new Exception("oclGroupedReduceSeqInitAggregate needs a static lane count")
      }
      val groups = m match {
        case Cst(value) => BigInt(value)
        case _ => throw new Exception("oclGroupedReduceSeqInitAggregate needs a static group count")
      }
      if (lanes <= 0 || (lanes & (lanes - 1)) != 0) {
        throw new Exception("oclGroupedReduceSeqInitAggregate needs a power-of-two lane count")
      }
      val outputLeaves = accLeaves(outDt, A)
      if (outputLeaves.size != groups.toInt) {
        throw new Exception(
          s"oclGroupedReduceSeqInitAggregate expected $groups aggregate leaves, got ${outputLeaves.size}")
      }
      val initLeaves = readLeaves(outDt, init)
      if (initLeaves.size != outputLeaves.size) {
        throw new Exception(
          s"oclGroupedReduceSeqInitAggregate init/output leaf mismatch: ${initLeaves.size} vs ${outputLeaves.size}")
      }
      con(input)(fun(expT((m * n)`.`dt, read))(x => {
        val total = m * n

        def writeRoots(root: BigInt => Phrase[ExpType]): Phrase[CommType] =
          initLeaves.zip(outputLeaves).zipWithIndex.foldLeft(Skip(): Phrase[CommType]) {
            case (body, ((initLeaf, outputLeaf), group)) =>
              body `;` copyReadInto(dt, f(initLeaf)(root(BigInt(group))), outputLeaf)
          }

        val firstFanIn =
          if (lanes >= 8) BigInt(8)
          else if (lanes >= 4) BigInt(4)
          else BigInt(2)
        val firstStride = lanes / firstFanIn
        val scratchLanes = Natural(Cst(firstStride.toLong))
        val scratchTotal = m * Cst(firstStride.toLong)

        def copyFirstStageInto(
            leaves: Seq[Phrase[ExpType]],
            dst: Phrase[AccType]
        ): Phrase[CommType] = {
          leaves match {
            case Seq(one) =>
              copyReadInto(dt, one, dst)
            case Seq(lhs, rhs) =>
              copyReadInto(dt, f(lhs)(rhs), dst)
            case _ =>
              val (lhsLeaves, rhsLeaves) = leaves.splitAt(leaves.size / 2)
              shine.OpenCL.DSL.`new`(AddressSpace.Private)(dt, lhs =>
                shine.OpenCL.DSL.`new`(AddressSpace.Private)(dt, rhs =>
                  copyFirstStageInto(lhsLeaves, lhs.wr) `;`
                    copyFirstStageInto(rhsLeaves, rhs.wr) `;`
                    copyReadInto(dt, f(lhs.rd)(rhs.rd), dst)))
          }
        }

        def firstStage(scratch: Phrase[VarType]): Phrase[CommType] =
          shine.OpenCL.DSL.parFor(shine.OpenCL.Local, 0, unroll = false)(
            scratchTotal,
            dt,
            scratch.wr,
            fun(expT(idx(scratchTotal), read))(q => fun(accT(dt))(dst => {
              val qNat = IndexAsNat(scratchTotal, q)
              val groupNat = qNat / scratchLanes
              val laneNat = qNat % scratchLanes
              val srcNat = (groupNat * Natural(n)) + (laneNat * Natural(Cst(firstFanIn.toLong)))
              def src(offset: BigInt): Phrase[ExpType] =
                x `@` NatAsIndex(total, srcNat + Natural(Cst(offset.toLong)))
              copyFirstStageInto((0 until firstFanIn.toInt).map(i => src(BigInt(i))), dst)
            }))
          ) `;` shine.OpenCL.DSL.barrier(local = true, global = false)

        def stage(stride: BigInt)(scratch: Phrase[VarType]): Phrase[CommType] = {
          val strideArith = Cst(stride.toLong)
          val strideNat = Natural(strideArith)
          val workItems = m * strideArith
          shine.OpenCL.DSL.parFor(shine.OpenCL.Local, 0, unroll = false)(
            workItems,
            dt,
            TakeAcc(workItems, scratchTotal - workItems, dt, scratch.wr),
            fun(expT(idx(workItems), read))(q => fun(accT(dt))(_ => {
              val qNat = IndexAsNat(workItems, q)
              val groupNat = qNat / strideNat
              val laneNat = qNat % strideNat
              val groupBase = groupNat * scratchLanes
              val dst = NatAsIndex(scratchTotal, groupBase + laneNat)
              val srcNat = groupBase + (laneNat * Natural(2))
              val src0 = NatAsIndex(scratchTotal, srcNat)
              val src1 = NatAsIndex(scratchTotal, srcNat + Natural(1))
              copyReadInto(dt, f(scratch.rd `@` src0)(scratch.rd `@` src1), scratch.wr `@` dst)
            }))
          ) `;` shine.OpenCL.DSL.barrier(local = true, global = false)
        }

        val strides = Iterator.iterate(firstStride / 2)(_ / 2).takeWhile(_ >= 2).toSeq
        comment("oclGroupedReduceSeqInitAggregate") `;` (
          if (lanes == 1) {
            writeRoots(group =>
              x `@` NatAsIndex(total, Natural(Cst(group.toLong)) * Natural(n)))
          } else {
            def root(scratch: Phrase[VarType], group: BigInt): Phrase[ExpType] = {
              val groupBase = Natural(Cst(group.toLong)) * scratchLanes
              val lhs = scratch.rd `@` NatAsIndex(scratchTotal, groupBase)
              if (firstStride == 1) {
                lhs
              } else {
                f(lhs)(scratch.rd `@` NatAsIndex(scratchTotal, groupBase + Natural(1)))
              }
            }
            shine.OpenCL.DSL.`new`(AddressSpace.Local)(scratchTotal`.`dt, scratch =>
              firstStage(scratch) `;`
                strides.foldLeft(Skip(): Phrase[CommType])((body, stride) =>
                  body `;` stage(stride)(scratch)) `;`
                writeRoots(group => root(scratch, group)))
          })
      }))

    case ocl.GroupedReducePrivateSeqInitAggregate(a, n, m, dt, outDt, f, init, input) =>
      if (a != AddressSpace.Local) {
        throw new Exception("oclGroupedReducePrivateSeqInitAggregate currently lowers local reductions only")
      }
      val lanes = n match {
        case Cst(value) => BigInt(value)
        case _ => throw new Exception("oclGroupedReducePrivateSeqInitAggregate needs a static lane count")
      }
      val groups = m match {
        case Cst(value) => BigInt(value)
        case _ => throw new Exception("oclGroupedReducePrivateSeqInitAggregate needs a static group count")
      }
      if (lanes <= 0 || (lanes & (lanes - 1)) != 0) {
        throw new Exception("oclGroupedReducePrivateSeqInitAggregate needs a power-of-two lane count")
      }
      val outputLeaves = accLeaves(outDt, A)
      if (outputLeaves.size != groups.toInt) {
        throw new Exception(
          s"oclGroupedReducePrivateSeqInitAggregate expected $groups aggregate leaves, got ${outputLeaves.size}")
      }
      val initLeaves = readLeaves(outDt, init)
      if (initLeaves.size != outputLeaves.size) {
        throw new Exception(
          s"oclGroupedReducePrivateSeqInitAggregate init/output leaf mismatch: ${initLeaves.size} vs ${outputLeaves.size}")
      }
      val total = m * n

      def writeRoots(root: BigInt => Phrase[ExpType]): Phrase[CommType] =
        initLeaves.zip(outputLeaves).zipWithIndex.foldLeft(Skip(): Phrase[CommType]) {
          case (body, ((initLeaf, outputLeaf), group)) =>
            body `;` copyReadInto(dt, f(initLeaf)(root(BigInt(group))), outputLeaf)
        }

      def stage(stride: BigInt)(scratch: Phrase[VarType]): Phrase[CommType] = {
        val strideArith = Cst(stride.toLong)
        val strideNat = Natural(strideArith)
        val workItems = m * strideArith
        shine.OpenCL.DSL.parFor(shine.OpenCL.Local, 0, unroll = false)(
          workItems,
          dt,
          TakeAcc(workItems, total - workItems, dt, scratch.wr),
          fun(expT(idx(workItems), read))(q => fun(accT(dt))(_ => {
            val qNat = IndexAsNat(workItems, q)
            val groupNat = qNat / strideNat
            val laneNat = qNat % strideNat
            val groupBase = groupNat * Natural(n)
            val dstNat = groupBase + laneNat
            val dst = NatAsIndex(total, dstNat)
            val src = NatAsIndex(total, dstNat + strideNat)
            copyReadInto(dt, f(scratch.rd `@` dst)(scratch.rd `@` src), scratch.wr `@` dst)
          }))
        ) `;` shine.OpenCL.DSL.barrier(local = true, global = false)
      }

      val strides = Iterator.iterate(lanes / 2)(_ / 2).takeWhile(_ >= 1).toSeq
      comment("oclGroupedReducePrivateSeqInitAggregate") `;`
        shine.OpenCL.DSL.`new`(AddressSpace.Local)(total`.`dt, scratch =>
          shine.OpenCL.DSL.parFor(shine.OpenCL.Local, 0, unroll = false)(
            total,
            dt,
            scratch.wr,
            fun(expT(idx(total), read))(q => fun(accT(dt))(dst =>
              copyReadInto(dt, input(q), dst)))
          ) `;` shine.OpenCL.DSL.barrier(local = true, global = false) `;`
            strides.foldLeft(Skip(): Phrase[CommType])((body, stride) =>
              body `;` stage(stride)(scratch)) `;`
            writeRoots(group =>
              scratch.rd `@` NatAsIndex(total, Natural(Cst(group.toLong)) * Natural(n))))

    case ocl.GroupedReduceSeqNested(a, n, m, dt, f, input) =>
      if (a != AddressSpace.Local) {
        throw new Exception("oclGroupedReduceSeqNested currently lowers local reductions only")
      }
      val lanes = n match {
        case Cst(value) => BigInt(value)
        case _ => throw new Exception("oclGroupedReduceSeqNested needs a static lane count")
      }
      if (lanes <= 0 || (lanes & (lanes - 1)) != 0) {
        throw new Exception("oclGroupedReduceSeqNested needs a power-of-two lane count")
      }
      con(input)(fun(expT(m`.`(n`.`dt), read))(x => {
        def directCopy(): Phrase[CommType] =
          `for`(m, group =>
            copyReadInto(dt, (x `@` group) `@` NatAsIndex(n, Natural(0)), A `@` group))

        val firstFanIn =
          if (lanes >= 8) BigInt(8)
          else if (lanes >= 4) BigInt(4)
          else BigInt(2)
        val firstStride = lanes / firstFanIn
        val scratchLanes = Natural(Cst(firstStride.toLong))
        val scratchTotal = m * Cst(firstStride.toLong)

        def copyFirstStageInto(
            leaves: Seq[Phrase[ExpType]],
            dst: Phrase[AccType]
        ): Phrase[CommType] = {
          leaves match {
            case Seq(one) =>
              copyReadInto(dt, one, dst)
            case Seq(lhs, rhs) =>
              copyReadInto(dt, f(lhs)(rhs), dst)
            case _ =>
              val (lhsLeaves, rhsLeaves) = leaves.splitAt(leaves.size / 2)
              shine.OpenCL.DSL.`new`(AddressSpace.Private)(dt, lhs =>
                shine.OpenCL.DSL.`new`(AddressSpace.Private)(dt, rhs =>
                  copyFirstStageInto(lhsLeaves, lhs.wr) `;`
                    copyFirstStageInto(rhsLeaves, rhs.wr) `;`
                    copyReadInto(dt, f(lhs.rd)(rhs.rd), dst)))
          }
        }

        def firstStage(scratch: Phrase[VarType]): Phrase[CommType] =
          shine.OpenCL.DSL.parFor(shine.OpenCL.Local, 0, unroll = false)(
            scratchTotal,
            dt,
            scratch.wr,
            fun(expT(idx(scratchTotal), read))(q => fun(accT(dt))(dst => {
              val qNat = IndexAsNat(scratchTotal, q)
              val groupNat = qNat / scratchLanes
              val laneNat = qNat % scratchLanes
              val group = NatAsIndex(m, groupNat)
              def src(offset: BigInt): Phrase[ExpType] =
                (x `@` group) `@` NatAsIndex(n, (laneNat * Natural(Cst(firstFanIn.toLong))) + Natural(Cst(offset.toLong)))
              copyFirstStageInto((0 until firstFanIn.toInt).map(i => src(BigInt(i))), dst)
            }))
          ) `;` shine.OpenCL.DSL.barrier(local = true, global = false)

        def stage(stride: BigInt)(scratch: Phrase[VarType]): Phrase[CommType] = {
          val strideArith = Cst(stride.toLong)
          val strideNat = Natural(strideArith)
          val workItems = m * strideArith
          shine.OpenCL.DSL.parFor(shine.OpenCL.Local, 0, unroll = false)(
            workItems,
            dt,
            TakeAcc(workItems, scratchTotal - workItems, dt, scratch.wr),
            fun(expT(idx(workItems), read))(q => fun(accT(dt))(_ => {
              val qNat = IndexAsNat(workItems, q)
              val groupNat = qNat / strideNat
              val laneNat = qNat % strideNat
              val groupBase = groupNat * scratchLanes
              val dst = NatAsIndex(scratchTotal, groupBase + laneNat)
              val srcNat = groupBase + (laneNat * Natural(2))
              val src0 = NatAsIndex(scratchTotal, srcNat)
              val src1 = NatAsIndex(scratchTotal, srcNat + Natural(1))
              copyReadInto(dt, f(scratch.rd `@` src0)(scratch.rd `@` src1), scratch.wr `@` dst)
            }))
          ) `;` shine.OpenCL.DSL.barrier(local = true, global = false)
        }

        val strides = Iterator.iterate(firstStride / 2)(_ / 2).takeWhile(_ >= 2).toSeq
        comment("oclGroupedReduceSeqNested") `;` (
          if (lanes == 1) {
            directCopy()
          } else {
            def root(scratch: Phrase[VarType], group: Phrase[ExpType]): Phrase[ExpType] = {
              val groupBase = IndexAsNat(m, group) * scratchLanes
              val lhs = scratch.rd `@` NatAsIndex(scratchTotal, groupBase)
              if (firstStride == 1) {
                lhs
              } else {
                f(lhs)(scratch.rd `@` NatAsIndex(scratchTotal, groupBase + Natural(1)))
              }
            }
            shine.OpenCL.DSL.`new`(AddressSpace.Local)(scratchTotal`.`dt, scratch =>
              firstStage(scratch) `;`
                strides.foldLeft(Skip(): Phrase[CommType])((body, stride) =>
                  body `;` stage(stride)(scratch)) `;`
                `for`(m, group =>
                  copyReadInto(dt, root(scratch, group), A `@` group)))
          })
      }))

    case ocl.GroupedReduceSeqInitAggregateNested(a, n, m, dt, outDt, f, init, input) =>
      if (a != AddressSpace.Local) {
        throw new Exception("oclGroupedReduceSeqInitAggregateNested currently lowers local reductions only")
      }
      val lanes = n match {
        case Cst(value) => BigInt(value)
        case _ => throw new Exception("oclGroupedReduceSeqInitAggregateNested needs a static lane count")
      }
      val groups = m match {
        case Cst(value) => BigInt(value)
        case _ => throw new Exception("oclGroupedReduceSeqInitAggregateNested needs a static group count")
      }
      if (lanes <= 0 || (lanes & (lanes - 1)) != 0) {
        throw new Exception("oclGroupedReduceSeqInitAggregateNested needs a power-of-two lane count")
      }
      val outputLeaves = accLeaves(outDt, A)
      if (outputLeaves.size != groups.toInt) {
        throw new Exception(
          s"oclGroupedReduceSeqInitAggregateNested expected $groups aggregate leaves, got ${outputLeaves.size}")
      }
      val initLeaves = readLeaves(outDt, init)
      if (initLeaves.size != outputLeaves.size) {
        throw new Exception(
          s"oclGroupedReduceSeqInitAggregateNested init/output leaf mismatch: ${initLeaves.size} vs ${outputLeaves.size}")
      }
      con(input)(fun(expT(m`.`(n`.`dt), read))(x => {
        def writeRoots(root: BigInt => Phrase[ExpType]): Phrase[CommType] =
          initLeaves.zip(outputLeaves).zipWithIndex.foldLeft(Skip(): Phrase[CommType]) {
            case (body, ((initLeaf, outputLeaf), group)) =>
              body `;` copyReadInto(dt, f(initLeaf)(root(BigInt(group))), outputLeaf)
          }

        val firstFanIn =
          if (lanes >= 8) BigInt(8)
          else if (lanes >= 4) BigInt(4)
          else BigInt(2)
        val firstStride = lanes / firstFanIn
        val scratchLanes = Natural(Cst(firstStride.toLong))
        val scratchTotal = m * Cst(firstStride.toLong)

        def copyFirstStageInto(
            leaves: Seq[Phrase[ExpType]],
            dst: Phrase[AccType]
        ): Phrase[CommType] = {
          leaves match {
            case Seq(one) =>
              copyReadInto(dt, one, dst)
            case Seq(lhs, rhs) =>
              copyReadInto(dt, f(lhs)(rhs), dst)
            case _ =>
              val (lhsLeaves, rhsLeaves) = leaves.splitAt(leaves.size / 2)
              shine.OpenCL.DSL.`new`(AddressSpace.Private)(dt, lhs =>
                shine.OpenCL.DSL.`new`(AddressSpace.Private)(dt, rhs =>
                  copyFirstStageInto(lhsLeaves, lhs.wr) `;`
                    copyFirstStageInto(rhsLeaves, rhs.wr) `;`
                    copyReadInto(dt, f(lhs.rd)(rhs.rd), dst)))
          }
        }

        def firstStage(scratch: Phrase[VarType]): Phrase[CommType] =
          shine.OpenCL.DSL.parFor(shine.OpenCL.Local, 0, unroll = false)(
            scratchTotal,
            dt,
            scratch.wr,
            fun(expT(idx(scratchTotal), read))(q => fun(accT(dt))(dst => {
              val qNat = IndexAsNat(scratchTotal, q)
              val groupNat = qNat / scratchLanes
              val laneNat = qNat % scratchLanes
              val group = NatAsIndex(m, groupNat)
              def src(offset: BigInt): Phrase[ExpType] =
                (x `@` group) `@` NatAsIndex(n, (laneNat * Natural(Cst(firstFanIn.toLong))) + Natural(Cst(offset.toLong)))
              copyFirstStageInto((0 until firstFanIn.toInt).map(i => src(BigInt(i))), dst)
            }))
          ) `;` shine.OpenCL.DSL.barrier(local = true, global = false)

        def stage(stride: BigInt)(scratch: Phrase[VarType]): Phrase[CommType] = {
          val strideArith = Cst(stride.toLong)
          val strideNat = Natural(strideArith)
          val workItems = m * strideArith
          shine.OpenCL.DSL.parFor(shine.OpenCL.Local, 0, unroll = false)(
            workItems,
            dt,
            TakeAcc(workItems, scratchTotal - workItems, dt, scratch.wr),
            fun(expT(idx(workItems), read))(q => fun(accT(dt))(_ => {
              val qNat = IndexAsNat(workItems, q)
              val groupNat = qNat / strideNat
              val laneNat = qNat % strideNat
              val groupBase = groupNat * scratchLanes
              val dst = NatAsIndex(scratchTotal, groupBase + laneNat)
              val srcNat = groupBase + (laneNat * Natural(2))
              val src0 = NatAsIndex(scratchTotal, srcNat)
              val src1 = NatAsIndex(scratchTotal, srcNat + Natural(1))
              copyReadInto(dt, f(scratch.rd `@` src0)(scratch.rd `@` src1), scratch.wr `@` dst)
            }))
          ) `;` shine.OpenCL.DSL.barrier(local = true, global = false)
        }

        val strides = Iterator.iterate(firstStride / 2)(_ / 2).takeWhile(_ >= 2).toSeq
        comment("oclGroupedReduceSeqInitAggregateNested") `;` (
          if (lanes == 1) {
            writeRoots(group =>
              (x `@` NatAsIndex(m, Natural(Cst(group.toLong)))) `@` NatAsIndex(n, Natural(0)))
          } else {
            def root(scratch: Phrase[VarType], group: BigInt): Phrase[ExpType] = {
              val groupBase = Natural(Cst(group.toLong)) * scratchLanes
              val lhs = scratch.rd `@` NatAsIndex(scratchTotal, groupBase)
              if (firstStride == 1) {
                lhs
              } else {
                f(lhs)(scratch.rd `@` NatAsIndex(scratchTotal, groupBase + Natural(1)))
              }
            }
            shine.OpenCL.DSL.`new`(AddressSpace.Local)(scratchTotal`.`dt, scratch =>
              firstStage(scratch) `;`
                strides.foldLeft(Skip(): Phrase[CommType])((body, stride) =>
                  body `;` stage(stride)(scratch)) `;`
                writeRoots(group => root(scratch, group)))
          })
      }))

    case kc@ocl.KernelCall(name, localSize, globalSize, n) =>
      def rec(ts: Seq[Phrase[ExpType]],
              es: Seq[Phrase[ExpType]]): Phrase[CommType] = {
        ts match {
          case Nil =>
            oclImp.KernelCallCmd(name, localSize, globalSize, n)(kc.inTs, kc.outT, kc.args, A)
          case Seq(arg, tail@_*) =>
            con(arg)(fun(expT(arg.t.dataType, read))(e => rec(tail, es :+ e)))
        }
      }

      rec(kc.args, Seq())

    case map@ocl.Map(level, dim) =>
      val (n, dt1, dt2, f, array) = map.unwrap
      con(array)(fun(expT(n `.` dt1, read))(x => {
        comment(s"map${level.toString}") `;`
          shine.OpenCL.DSL.parFor(level, dim, unroll = false)(n, dt2, A,
            fun(expT(idx(n), read))(i => fun(accT(dt2))(a => acc(f(x `@` i))(a))))
      }))

    case fc@ocl.OpenCLFunctionCall(name, n) =>
      def rec(ts: Seq[(Phrase[ExpType], DataType)],
                  exps: Seq[Phrase[ExpType]],
                  inTs: Seq[DataType]): Phrase[CommType] = {
        ts match {
          // with only one argument left to process return the assignment of the OpenCLFunction call
          case Seq( (arg, inT) ) =>
            con(arg)(fun(expT(inT, read))(e =>
              A :=|fc.outT| ocl.OpenCLFunctionCall(name, n)(inTs :+ inT, fc.outT, exps :+ e) ))
          // with a `tail` of arguments left, recurse
          case Seq( (arg, inT), tail@_* ) =>
            con(arg)(fun(expT(inT, read))(e => rec(tail, exps :+ e, inTs :+ inT) ))
        }
      }

      rec(fc.args zip fc.inTs, Seq(), Seq())

    // CUDA
    case cuda.AsFragment(rows, columns, layers, dataType, fragmentKind, layout, matrix) =>
      con(matrix)(fun(ExpType(ArrayType(rows, ArrayType(columns, dataType)), read))(matrix =>
        cudaImp.WmmaLoad(rows, columns, layers, dataType, fragmentKind, layout, matrix, A)))

    case cuda.AsMatrix(rows, columns, layers, dataType, fragment) =>
      con(fragment)(fun(ExpType(fragment.t.dataType, read))(fragment =>
        cudaImp.WmmaStore(rows, columns, layers, dataType, fragment, A)))

    case cuda.GenerateFragment(rows, columns, layers, dataType, frag, layout, fill) =>
      con(fill)(fun(ExpType(dataType, read))(fill =>
        cudaImp.WmmaFill(rows, columns, layers, dataType, frag, layout, fill, A)))

    case map@cuda.Map(level, dim) =>
      val (n, dt1, dt2, f, array) = map.unwrap
      con(array)(fun(expT(n `.` dt1, read))(x => {
        val forLoop = comment(s"map${level.toString}") `;`
          shine.cuda.DSL.parFor(level, dim, unroll = false)(n, dt2, A,
            fun(expT(idx(n), read))(i => fun(accT(dt2))(a =>
              acc(f(x `@` i))(a))))
        //TODO use other InsertMemoryBarrieres-mechanism
        level match {
          case shine.OpenCL.Local => forLoop `;` cudaImp.SyncThreads()
          case shine.OpenCL.Warp => forLoop `;` cudaImp.SyncThreads()
          case shine.OpenCL.Lane => forLoop `;` cudaImp.SyncWarp()
          case _ => forLoop
        }
      }))

    case cuda.MapFragment(rows, columns, layers, dt, frag, layout, f, input) =>
      con(input)(fun(expT(FragmentType(rows, columns, layers, dt, frag, layout), read))(input =>
        shine.cuda.primitives.imperative.ForFragment(rows, columns, layers, dt, frag, layout, input, A,
          fun(expT(dt, read))(x =>
            fun(accT(dt))(o =>
              acc(f(x))(o))))))

    case cuda.TensorMatMultAdd(m, n, k, layoutA, layoutB, dataType, dataTypeAcc, aMatrix, bMatrix, cMatrix) =>
      con(aMatrix)(fun(ExpType(FragmentType(m, n, k, dataType, Fragment.AMatrix, layoutA), read))(aMatrix =>
        con(bMatrix)(fun(ExpType(FragmentType(m, n, k, dataType, Fragment.BMatrix, layoutB), read))(bMatrix =>
          con(cMatrix)(fun(ExpType(FragmentType(m, n, k, dataTypeAcc, Fragment.Accumulator, MatrixLayout.None), read))(cMatrix =>
            cudaImp.WmmaMMA(m, n, k, layoutA, layoutB, dataType, dataTypeAcc, aMatrix, bMatrix, cMatrix, A)))))))

    //GAP8
    case r@shine.GAP8.primitives.functional.Run(cores) => {
      ???
    }


    case kc@shine.GAP8.primitives.functional.KernelCall(name, cores, n) =>
      def rec(ts: Seq[Phrase[ExpType]], es: Seq[Phrase[ExpType]]): Phrase[CommType] = ts match {
        case Nil =>
          shine.GAP8.primitives.imperative.KernelCallCmd(name, cores, n)(kc.inTs, kc.outT, kc.args, A)
        case Seq(arg, tail@_*) =>
          con(arg)(fun(expT(arg.t.dataType, read))(e => rec(tail, es :+ e)))
      }

      rec(kc.args, Seq())
    }
  }

  private def localOwnerCondition: Phrase[ExpType] = {
    def isZero(dim: Int): Phrase[ExpType] =
      BinOp(Operators.Binary.EQ, Natural(get_local_id(dim)), Natural(0))

    BinOp(Operators.Binary.AND,
      BinOp(Operators.Binary.AND, isZero(0), isZero(1)),
      isZero(2))
  }
}
