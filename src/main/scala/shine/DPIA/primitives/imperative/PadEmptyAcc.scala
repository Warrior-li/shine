package shine.DPIA.primitives.imperative

import arithexpr.arithmetic._
import shine.DPIA.Phrases._
import shine.DPIA.Types._
import rise.core.types.{ FunType => _, DepFunType => _, TypePlaceholder => _, TypeIdentifier => _, ExprType => _, _ }
import rise.core.types.DataType._
import rise.core.types.Kind.{ Identifier => _, _ }
import shine.DPIA._

final case class PadEmptyAcc(val n: Nat, val r: Nat, val dt: DataType, val array: Phrase[AccType]) extends AccPrimitive {
  assert {
    array :: accT(ArrayType(n, dt))
    true
  }
  override val t: AccType = accT(ArrayType(n + r, dt))
  override def visitAndRebuild(v: VisitAndRebuild.Visitor): PadEmptyAcc =
    new PadEmptyAcc(v.nat(n), v.nat(r), v.data(dt), VisitAndRebuild(array, v))
}
