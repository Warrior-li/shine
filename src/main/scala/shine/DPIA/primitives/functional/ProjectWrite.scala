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
final case class ProjectWrite(val n: Nat, val m: Nat, val dt: DataType, val a: Access, val indices: Phrase[ExpType], val input: Phrase[ExpType]) extends ExpPrimitive {
  assert {
    indices :: expT(ArrayType(n, IndexType(m)), read)
    input :: expT(ArrayType(n, dt), a)
    true
  }
  override val t: ExpType = expT(ArrayType(m, dt), write)
  override def visitAndRebuild(v: VisitAndRebuild.Visitor): ProjectWrite = new ProjectWrite(v.nat(n), v.nat(m), v.data(dt), v.access(a), VisitAndRebuild(indices, v), VisitAndRebuild(input, v))
}
