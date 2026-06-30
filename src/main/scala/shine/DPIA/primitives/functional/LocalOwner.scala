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
final case class LocalOwner(val dt: DataType, val input: Phrase[ExpType]) extends ExpPrimitive {
  assert {
    input :: expT(dt, read)
    true
  }
  override val t: ExpType = expT(dt, write)
  override def visitAndRebuild(v: VisitAndRebuild.Visitor): LocalOwner =
    new LocalOwner(v.data(dt), VisitAndRebuild(input, v))
}
