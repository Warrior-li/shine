// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! //
// This file follows the generated primitive shape used in this directory.  //
// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! //
package shine.DPIA.primitives.functional
import arithexpr.arithmetic._
import shine.DPIA.Phrases._
import shine.DPIA.Types._
import rise.core.types.{ FunType => _, DepFunType => _, TypePlaceholder => _, TypeIdentifier => _, ExprType => _, _ }
import rise.core.types.DataType._
import rise.core.types.Kind.{ Identifier => _, _ }
import shine.DPIA._

final case class StaticIterate(val n: Nat, val dt: DataType, val f: Phrase[FunType[ExpType, FunType[ExpType, ExpType]]], val init: Phrase[ExpType]) extends ExpPrimitive {
  assert {
    f :: FunType(expT(IndexType(n), read), FunType(expT(dt, read), expT(dt, read)))
    init :: expT(dt, read)
    true
  }
  override val t: ExpType = expT(dt, read)
  override def visitAndRebuild(v: VisitAndRebuild.Visitor): StaticIterate =
    new StaticIterate(v.nat(n), v.data(dt), VisitAndRebuild(f, v), VisitAndRebuild(init, v))
  def unwrap: (Nat, DataType, Phrase[FunType[ExpType, FunType[ExpType, ExpType]]], Phrase[ExpType]) =
    (n, dt, f, init)
}
