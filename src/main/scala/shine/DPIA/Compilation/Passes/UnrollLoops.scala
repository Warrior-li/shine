package shine.DPIA.Compilation.Passes

import arithexpr.arithmetic.ArithExpr.isSmaller
import arithexpr.arithmetic.Cst
import shine.DPIA.Nat
import shine.DPIA.Phrases.{Natural, Phrase, VisitAndRebuild}
import shine.DPIA.Types.{CommType, PhraseType}
import shine.DPIA.primitives.functional.NatAsIndex
import shine.DPIA.primitives.imperative._
import shine.OpenCL.primitives.imperative.ParFor

object UnrollLoops {
  private val defaultMaxStaticUnrollIterations = 1

  private def maxStaticUnrollIterations: Int =
    sys.props
      .get("shine.unroll.maxStaticIterations")
      .flatMap(s => scala.util.Try(s.toInt).toOption)
      .getOrElse(defaultMaxStaticUnrollIterations)

  def unroll: Phrase[CommType] => Phrase[CommType] = p => {
    val r = VisitAndRebuild(p, new VisitAndRebuild.Visitor {
      override def phrase[T <: PhraseType](p: Phrase[T]): Result[Phrase[T]] =
        p match {
          case f@For(true) if shouldUnroll(f.n, init = 0, step = 1) =>
            f.loopBody match {
              case shine.DPIA.Phrases.Lambda(x, body) =>
                Continue(unrollLoop(f.n, init = 0, step = 1, i =>
                  Phrase.substitute(NatAsIndex(f.n, Natural(i)),
                    `for` = x, in = body)), this)
              case _ => throw new Exception("This should not happen")
            }
          case f@For(true) =>
            Continue(For(unroll = false)(f.n, f.loopBody), this)
          case f@ForNat(true) if shouldUnroll(f.n, init = 0, step = 1) =>
            f.loopBody match {
              case shine.DPIA.Phrases.DepLambda(kind, x, body) =>
                Continue(unrollLoop(f.n, init = 0, step = 1, i =>
                  shine.DPIA.Types.substitute(i, `for` = x, in = body)), this)
              case _ => throw new Exception("This should not happen")
            }
          case f@ForNat(true) =>
            Continue(ForNat(unroll = false)(f.n, f.loopBody), this)
          case pf@ParFor(_, _, true, _) if shouldUnroll(pf.n, pf.init, pf.step) =>
            pf.body match {
              case shine.DPIA.Phrases.Lambda(ident, shine.DPIA.Phrases.Lambda(identOut, body)) =>
                pf.out.t.dataType match {
                  case rise.core.types.DataType.ArrayType(_, elemType) =>
                    Continue(unrollLoop(pf.n, pf.init, pf.step, i =>
                      Phrase.substitute(
                        IdxAcc(pf.n, elemType,
                          NatAsIndex(pf.n, Natural(i)), pf.out),
                        `for` = identOut,
                        Phrase.substitute(NatAsIndex(pf.n, Natural(i)),
                          `for` = ident, in = body))), this)
                  case _ =>
                    throw new Exception("OpenCLParFor acceptor has to be of ArrayType.")
                }
              case _ => throw new Exception("This should not happen")
            }
          case pf@ParFor(level, dim, true, name) =>
            Continue(ParFor(level, dim, unroll = false, name)(
              pf.init, pf.n, pf.step, pf.dt, pf.out, pf.body), this)
          case _ =>
            Continue(p, this)
        }
    })
    r
  }

  private def shouldUnroll(n: Nat, init: Nat, step: Nat): Boolean =
    try {
      numIterations(n, init, step) <= maxStaticUnrollIterations
    } catch {
      case _: arithexpr.arithmetic.NotEvaluableException => false
    }

  private def numIterations(n: Nat, init: Nat, step: Nat): Int = {
    import arithexpr.arithmetic.NotEvaluableException

    val stopMax = try {
      n.max.eval
    } catch {
      case e: NotEvaluableException =>
        throw e
    }

    val startMin = try {
      init.min.eval
    } catch {
      case e: NotEvaluableException =>
        throw e
    }

    val incr = try {
      step.eval
    } catch {
      case e: NotEvaluableException =>
        throw e
    }

    ceilDiv(stopMax - startMin, incr)
  }

  private def unrollLoop(n: Nat, init: Nat, step: Nat,
                         genBody: Nat => Phrase[CommType]): Phrase[CommType] = {
    import arithexpr.arithmetic.NotEvaluableException

    val numIter = numIterations(n, init, step)
    val incr = try {
      step.eval
    } catch {
      case _: NotEvaluableException =>
        throw new Exception(s"cannot evaluate $step during loop unrolling")
    }

    val tmp = (0 until numIter).foldLeft[Phrase[CommType]](
      shine.DPIA.DSL.comment(s"unrolling loop of $numIter"))({
      case (prev, i) =>
        val index = init + Cst(i * incr)
        assert(isSmaller(index, n).contains(true)) //TODO add if-guards otherwise.
        //TODO store result of init in temporary variable
        Seq(prev, genBody(index))
    })

    tmp
  }

  private def ceilDiv(a: Int, b: Int): Int = {
    (a + b - 1) / b
  }
}
