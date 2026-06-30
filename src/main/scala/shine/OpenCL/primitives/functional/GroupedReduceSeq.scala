// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! //
// This file follows the generated primitive shape used in this directory.  //
// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! //
package shine.OpenCL.primitives.functional
import arithexpr.arithmetic._
import shine.DPIA.Phrases._
import shine.DPIA.Types._
import rise.core.types.{ FunType => _, DepFunType => _, TypePlaceholder => _, TypeIdentifier => _, ExprType => _, _ }
import rise.core.types.DataType._
import rise.core.types.Kind.{ Identifier => _, _ }
import shine.DPIA._

final case class GroupedReduceSeq(
  val a: AddressSpace,
  val n: Nat,
  val m: Nat,
  val dt: DataType,
  val f: Phrase[FunType[ExpType, FunType[ExpType, ExpType]]],
  val input: Phrase[ExpType]
) extends ExpPrimitive {
  assert {
    f :: FunType(expT(dt, read), FunType(expT(dt, read), expT(dt, read)))
    input :: expT(ArrayType(m * n, dt), read)
    true
  }
  override val t: ExpType = expT(ArrayType(m, dt), read)
  override def visitAndRebuild(v: VisitAndRebuild.Visitor): GroupedReduceSeq =
    new GroupedReduceSeq(v.addressSpace(a), v.nat(n), v.nat(m), v.data(dt), VisitAndRebuild(f, v), VisitAndRebuild(input, v))
}
