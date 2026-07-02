package shine.DPIA.primitives.imperative

import arithexpr.arithmetic._
import shine.DPIA.Phrases._
import shine.DPIA.Types._
import rise.core.types.{ FunType => _, DepFunType => _, TypePlaceholder => _, TypeIdentifier => _, ExprType => _, _ }
import rise.core.types.DataType._
import rise.core.types.Kind.{ Identifier => _, _ }
import shine.DPIA._

final case class ProjectWriteAcc(
    val n: Nat,
    val m: Nat,
    val total: Nat,
    val sourceT: DataType,
    val leafT: DataType,
    val flatBase: Phrase[ExpType],
    val indices: Phrase[ExpType],
    val array: Phrase[AccType])
  extends AccPrimitive {
  assert {
    flatBase :: expT(NatType, read)
    indices :: expT(ArrayType(total, IndexType(m)), read)
    array :: accT(ArrayType(m, leafT))
    true
  }

  override val t: AccType = accT(sourceT)

  override def visitAndRebuild(v: VisitAndRebuild.Visitor): ProjectWriteAcc =
    new ProjectWriteAcc(
      v.nat(n),
      v.nat(m),
      v.nat(total),
      v.data(sourceT),
      v.data(leafT),
      VisitAndRebuild(flatBase, v),
      VisitAndRebuild(indices, v),
      VisitAndRebuild(array, v))
}
