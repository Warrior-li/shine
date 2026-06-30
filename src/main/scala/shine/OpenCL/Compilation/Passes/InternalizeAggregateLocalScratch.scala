package shine.OpenCL.Compilation.Passes

import arithexpr.arithmetic.Cst
import rise.core.types.AddressSpace
import rise.core.types.DataType
import rise.core.types.DataType.{ArrayType => RiseArrayType, PairType}
import shine.C
import shine.C.AST._
import shine.OpenCL
import shine.OpenCL.{GlobalSize, LocalSize, NDRange}
import shine.OpenCL.Compilation.Passes.HoistMemoryAllocations.AllocationInfo

/**
 * Keep statically-sized aggregate local scratch inside the kernel body.
 *
 * Hoisted local allocations normally become dynamic `__local` kernel
 * parameters.  That is appropriate for ordinary local tiles, but aggregate
 * local-reduction scratch such as `[K](vec16 x vec16)` explodes into many
 * flattened local parameters after struct flattening.  When the scratch size is
 * static, a work-group scoped `__local T buf[N]` declaration is the standard
 * OpenCL form and avoids unnecessary host ABI growth.
 */
object InternalizeAggregateLocalScratch {
  def internalize(
      allocations: Seq[AllocationInfo],
      params: Seq[ParamDecl],
      body: Stmt,
      wgConfig: Option[(LocalSize, GlobalSize)] = None
    ): (Seq[ParamDecl], Stmt) = {
    val candidateLocalInfo = allocations.collect {
      case AllocationInfo(AddressSpace.Local, identifier)
          if staticLocalArray(identifier.t.t1.dataType).isDefined =>
        identifier.name -> (
          staticLocalArray(identifier.t.t1.dataType).get,
          containsPair(identifier.t.t1.dataType))
    }.toMap

    val nonLocalParamNames = params.collect {
      case p if !isLocalPointer(p) => p.name
    }.toSet

    val localWorkItems = workGroupItemCount(wgConfig)
    val aggregateLocalSizes =
      candidateLocalInfo.flatMap {
        case (root, (size, hasPair)) if !shouldInternalize(root, hasPair, body, nonLocalParamNames) =>
          None

        case (root, (size, hasPair))
            if params.exists(p =>
              rootName(p.name, Map(root -> size)).contains(root) &&
                hasNonZeroOrDynamicIndexUse(body, p.name)) =>
          localWorkItems.map { workItems =>
            val required = if (hasPair) workItems else workItems * Cst(2)
            root -> maxStatic(size, required)
          }
        case (root, (size, _)) =>
          Some(root -> size)
      }

    if (aggregateLocalSizes.isEmpty) {
      params -> body
    } else {
      val (internalized, kept) = params.partition(p =>
        aggregateLocalSizes.keys.exists(root => p.name == root || p.name.startsWith(root + "_")))

      val decls = internalized.flatMap { p =>
        rootName(p.name, aggregateLocalSizes).flatMap { root =>
          p.t match {
            case OpenCL.AST.PointerType(AddressSpace.Local, valueType, const) =>
              Some(DeclStmt(OpenCL.AST.VarDecl(
                p.name,
                C.AST.ArrayType(valueType, Some(aggregateLocalSizes(root)), const),
                AddressSpace.Local,
                None)))
            case _ => None
          }
        }
      }

      kept -> prepend(body, decls)
    }
  }

  private def rootName(
      paramName: String,
      roots: Map[String, arithexpr.arithmetic.ArithExpr]
    ): Option[String] =
    roots.keys.toSeq.sortBy(-_.length).find(root =>
      paramName == root || paramName.startsWith(root + "_"))

  private def prepend(body: Stmt, decls: Seq[Stmt]): Stmt =
    if (decls.isEmpty) {
      body
    } else {
      body match {
        case Block(stmts) => Block(decls ++ stmts)
        case other => Block(decls :+ other)
      }
    }

  private def staticLocalArray(dt: DataType): Option[arithexpr.arithmetic.ArithExpr] =
    dt match {
      case RiseArrayType(n, _) => Some(n)
      case _ => None
    }

  private def maxStatic(
      a: arithexpr.arithmetic.ArithExpr,
      b: arithexpr.arithmetic.ArithExpr
    ): arithexpr.arithmetic.ArithExpr =
    (a, b) match {
      case (Cst(x), Cst(y)) => Cst(math.max(x, y))
      case _ => a
    }

  private def shouldInternalize(
      root: String,
      hasPair: Boolean,
      body: Stmt,
      nonLocalParamNames: Set[String]
    ): Boolean = {
    if (hasPair) {
      true
    } else {
      val writes = localWritesTo(root, body)
      writes.nonEmpty && writes.forall(rhs => !referencesAny(rhs, nonLocalParamNames))
    }
  }

  private def containsPair(dt: DataType): Boolean =
    dt match {
      case PairType(_, _) => true
      case RiseArrayType(_, elem) => containsPair(elem)
      case _ => false
    }

  private def isLocalPointer(p: ParamDecl): Boolean =
    p.t match {
      case OpenCL.AST.PointerType(AddressSpace.Local, _, _) => true
      case _ => false
    }

  private def localWritesTo(root: String, stmt: Stmt): Seq[Expr] =
    stmt match {
      case Block(body) => body.flatMap(localWritesTo(root, _))
      case Stmts(a, b) => localWritesTo(root, a) ++ localWritesTo(root, b)
      case ForLoop(init, cond, increment, body) =>
        localWritesTo(root, init) ++ localWritesTo(root, body)
      case WhileLoop(_, body) => localWritesTo(root, body)
      case IfThenElse(_, trueBody, falseBody) =>
        localWritesTo(root, trueBody) ++ falseBody.toSeq.flatMap(localWritesTo(root, _))
      case ExprStmt(Assignment(lhs, rhs)) if referencesName(lhs, root) =>
        Seq(rhs)
      case _ => Seq.empty
    }

  private def referencesAny(expr: Expr, names: Set[String]): Boolean =
    expr match {
      case DeclRef(name) => names.contains(name)
      case ArraySubscript(array, index) =>
        referencesAny(array, names) || referencesAny(index, names)
      case Assignment(lhs, rhs) =>
        referencesAny(lhs, names) || referencesAny(rhs, names)
      case UnaryExpr(_, e) => referencesAny(e, names)
      case BinaryExpr(lhs, _, rhs) =>
        referencesAny(lhs, names) || referencesAny(rhs, names)
      case TernaryExpr(c, t, f) =>
        referencesAny(c, names) || referencesAny(t, names) || referencesAny(f, names)
      case FunCall(_, args) => args.exists(referencesAny(_, names))
      case Cast(_, e) => referencesAny(e, names)
      case StructMemberAccess(e, _) => referencesAny(e, names)
      case _ => false
    }

  private def referencesName(expr: Expr, name: String): Boolean =
    expr match {
      case DeclRef(`name`) => true
      case ArraySubscript(array, index) =>
        referencesName(array, name) || referencesName(index, name)
      case Assignment(lhs, rhs) =>
        referencesName(lhs, name) || referencesName(rhs, name)
      case UnaryExpr(_, e) => referencesName(e, name)
      case BinaryExpr(lhs, _, rhs) =>
        referencesName(lhs, name) || referencesName(rhs, name)
      case TernaryExpr(c, t, f) =>
        referencesName(c, name) || referencesName(t, name) || referencesName(f, name)
      case FunCall(_, args) => args.exists(referencesName(_, name))
      case Cast(_, e) => referencesName(e, name)
      case StructMemberAccess(e, _) => referencesName(e, name)
      case _ => false
    }

  private def workGroupItemCount(
      wgConfig: Option[(LocalSize, GlobalSize)]
    ): Option[arithexpr.arithmetic.ArithExpr] =
    wgConfig.collect {
      case (LocalSize(NDRange(Cst(x), Cst(y), Cst(z))), _) => Cst(x * y * z)
    }

  private def hasNonZeroOrDynamicIndexUse(stmt: Stmt, name: String): Boolean =
    stmt match {
      case Block(body) => body.exists(hasNonZeroOrDynamicIndexUse(_, name))
      case Stmts(a, b) => hasNonZeroOrDynamicIndexUse(a, name) || hasNonZeroOrDynamicIndexUse(b, name)
      case ForLoop(init, cond, increment, body) =>
        hasNonZeroOrDynamicIndexUse(init, name) ||
          hasNonZeroOrDynamicIndexUse(ExprStmt(cond), name) ||
          hasNonZeroOrDynamicIndexUse(ExprStmt(increment), name) ||
          hasNonZeroOrDynamicIndexUse(body, name)
      case WhileLoop(cond, body) =>
        hasNonZeroOrDynamicIndexUse(ExprStmt(cond), name) || hasNonZeroOrDynamicIndexUse(body, name)
      case IfThenElse(cond, trueBody, falseBody) =>
        hasNonZeroOrDynamicIndexUse(ExprStmt(cond), name) ||
          hasNonZeroOrDynamicIndexUse(trueBody, name) ||
          falseBody.exists(hasNonZeroOrDynamicIndexUse(_, name))
      case DeclStmt(v: OpenCL.AST.VarDecl) => v.init.exists(hasNonZeroOrDynamicIndexUse(_, name))
      case DeclStmt(v: VarDecl) => v.init.exists(hasNonZeroOrDynamicIndexUse(_, name))
      case ExprStmt(expr) => hasNonZeroOrDynamicIndexUse(expr, name)
      case _ => false
    }

  private def hasNonZeroOrDynamicIndexUse(expr: Expr, name: String): Boolean =
    expr match {
      case ArraySubscript(DeclRef(n), index) if n == name => !isZeroIndex(index)
      case ArraySubscript(array, index) =>
        hasNonZeroOrDynamicIndexUse(array, name) || hasNonZeroOrDynamicIndexUse(index, name)
      case Assignment(lhs, rhs) =>
        hasNonZeroOrDynamicIndexUse(lhs, name) || hasNonZeroOrDynamicIndexUse(rhs, name)
      case UnaryExpr(_, e) => hasNonZeroOrDynamicIndexUse(e, name)
      case BinaryExpr(lhs, _, rhs) =>
        hasNonZeroOrDynamicIndexUse(lhs, name) || hasNonZeroOrDynamicIndexUse(rhs, name)
      case TernaryExpr(c, t, f) =>
        hasNonZeroOrDynamicIndexUse(c, name) ||
          hasNonZeroOrDynamicIndexUse(t, name) ||
          hasNonZeroOrDynamicIndexUse(f, name)
      case FunCall(_, args) => args.exists(hasNonZeroOrDynamicIndexUse(_, name))
      case Cast(_, e) => hasNonZeroOrDynamicIndexUse(e, name)
      case StructMemberAccess(e, _) => hasNonZeroOrDynamicIndexUse(e, name)
      case _ => false
    }

  private def isZeroIndex(index: Expr): Boolean =
    index match {
      case Literal(text) => text.trim == "0"
      case ArithmeticExpr(Cst(0)) => true
      case Cast(_, e) => isZeroIndex(e)
      case _ => false
    }
}
