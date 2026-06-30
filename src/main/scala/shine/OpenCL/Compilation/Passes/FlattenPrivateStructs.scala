package shine.OpenCL.Compilation.Passes

import rise.core.types.AddressSpace
import shine.C
import shine.C.AST._
import shine.OpenCL

/**
 * Flatten private struct variables into scalar/vector leaf variables.
 *
 * Pair-tree accumulators lower to nested C structs such as
 * `Record_(Record_float16_float16, ...)`.  OpenCL compilers often handle this
 * worse than explicit private scalar/vector temporaries.  This pass is
 * deliberately conservative: it only rewrites block-local struct variables that
 * are declared without an initializer and whose uses are all complete leaf-field
 * accesses.  Kernel parameters, local/global memory objects, whole-struct
 * values, and partially accessed structs are left untouched.
 */
object FlattenPrivateStructs {
  private case class Leaf(path: List[String], t: Type)
  private sealed trait Shape
  private case object ValueShape extends Shape
  private case class ArrayShape(size: Option[arithexpr.arithmetic.ArithExpr], const: Boolean, addressSpace: AddressSpace) extends Shape
  private case class PointerShape(const: Boolean, addressSpace: AddressSpace) extends Shape

  private case class Flattened(root: String, leaves: Seq[Leaf], shape: Shape) {
    def leafName(path: List[String]): String =
      (root +: path.map {
        case "_fst" => "fst"
        case "_snd" => "snd"
        case other => other.stripPrefix("_")
      }).mkString("_")
  }

  private def withInit(decl: VarDecl, init: Option[Expr]): VarDecl =
    decl match {
      case v: OpenCL.AST.VarDecl =>
        OpenCL.AST.VarDecl(v.name, v.t, v.addressSpace, init)
      case v =>
        VarDecl(v.name, v.t, init)
    }

  def flatten(body: Stmt): Stmt =
    rewriteStmt(body, Map.empty)

  def flattenKernel(params: Seq[ParamDecl], body: Stmt): (Seq[ParamDecl], Stmt) = {
    val env = params.collect {
      case ParamDecl(name, OpenCL.AST.PointerType(AddressSpace.Local, t: C.AST.StructType, const)) =>
        leaves(t).map(name -> Flattened(name, _, PointerShape(const, AddressSpace.Local)))
    }.flatten.toMap
    val rewrittenParams = params.flatMap {
      case ParamDecl(name, OpenCL.AST.PointerType(AddressSpace.Local, _: C.AST.StructType, _))
          if env.contains(name) =>
        env(name).leaves.map { leaf =>
          ParamDecl(env(name).leafName(leaf.path),
            OpenCL.AST.PointerType(AddressSpace.Local, leaf.t))
        }
      case other =>
        Seq(other)
    }
    rewrittenParams -> rewriteStmt(body, env)
  }

  private def rewriteStmt(stmt: Stmt, env: Map[String, Flattened]): Stmt =
    stmt match {
      case Block(body) =>
        val declaredNames = collectDeclaredNames(body)
        val localCandidates = collectFlattenableDeclarations(body)
        val valid = localCandidates.filter { case (name, flattened) =>
          (flattened.shape != ValueShape || validUses(body, name, flattened)) &&
            flattened.leaves.forall { leaf =>
              val leafName = flattened.leafName(leaf.path)
              leafName == name || !declaredNames(leafName)
            }
        }
        val localEnv = env ++ valid
        val rewritten = body.flatMap {
          case DeclStmt(VarDecl(name, _: C.AST.StructType, None)) if valid.contains(name) =>
            valid(name).leaves.map(leaf => DeclStmt(leafDecl(valid(name), leaf, None)))
          case DeclStmt(v @ OpenCL.AST.VarDecl(name, C.AST.ArrayType(_: C.AST.StructType, _, _), _, _))
              if valid.contains(name) =>
            valid(name).leaves.map(leaf => DeclStmt(leafDecl(valid(name), leaf, v.init)))
          case DeclStmt(v @ OpenCL.AST.VarDecl(name, OpenCL.AST.PointerType(AddressSpace.Local, _: C.AST.StructType, _), _, _))
              if valid.contains(name) =>
            valid(name).leaves.map { leaf =>
              DeclStmt(leafDecl(valid(name), leaf,
                v.init.map(rewriteExprForLeafWithTextFallback(_, leaf.path, localEnv))))
            }
          case ExprStmt(Assignment(DeclRef(name), rhs)) if localEnv.contains(name) =>
            localEnv(name).leaves.map { leaf =>
              ExprStmt(Assignment(
                DeclRef(localEnv(name).leafName(leaf.path)),
                rewriteExprForLeafWithTextFallback(rhs, leaf.path, localEnv)
              ))
            }
          case other =>
            Seq(rewriteStmt(other, localEnv))
        }
        Block(rewritten)

      case Stmts(a, b) =>
        Stmts(rewriteStmt(a, env), rewriteStmt(b, env))

      case ForLoop(init, cond, increment, body) =>
        ForLoop(
          rewriteStmt(init, env).asInstanceOf[DeclStmt],
          rewriteExpr(cond, env),
          rewriteExpr(increment, env),
          rewriteStmt(body, env).asInstanceOf[Block]
        )

      case WhileLoop(cond, body) =>
        WhileLoop(rewriteExpr(cond, env), rewriteStmt(body, env))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(
          rewriteExpr(cond, env),
          rewriteStmt(trueBody, env),
          falseBody.map(rewriteStmt(_, env))
        )

      case DeclStmt(v @ VarDecl(_, _, init)) =>
        DeclStmt(withInit(v, init.map(rewriteExpr(_, env))))

      case ExprStmt(Assignment(lhs, rhs)) =>
        ExprStmt(Assignment(rewriteExpr(lhs, env), rewriteExpr(rhs, env)))

      case ExprStmt(expr) =>
        ExprStmt(rewriteExpr(expr, env))

      case other =>
        other
    }

  private def collectFlattenableDeclarations(body: Seq[Stmt]): Map[String, Flattened] =
    body.collect {
      case DeclStmt(VarDecl(name, t: C.AST.StructType, None)) =>
        leaves(t).map(ls => name -> Flattened(name, ls, ValueShape))
      case DeclStmt(OpenCL.AST.VarDecl(name, C.AST.ArrayType(t: C.AST.StructType, size, const), addressSpace @ AddressSpace.Local, None)) =>
        leaves(t).map(ls => name -> Flattened(name, ls, ArrayShape(size, const, addressSpace)))
      case DeclStmt(OpenCL.AST.VarDecl(name, OpenCL.AST.PointerType(addressSpace @ AddressSpace.Local, t: C.AST.StructType, const), _, _)) =>
        leaves(t).map(ls => name -> Flattened(name, ls, PointerShape(const, addressSpace)))
    }.flatten.toMap

  private def leafDecl(flattened: Flattened, leaf: Leaf, init: Option[Expr]): VarDecl =
    flattened.shape match {
      case ValueShape =>
        VarDecl(flattened.leafName(leaf.path), leaf.t, init)
      case ArrayShape(size, const, addressSpace) =>
        OpenCL.AST.VarDecl(
          flattened.leafName(leaf.path),
          C.AST.ArrayType(leaf.t, size, const),
          addressSpace,
          init
        )
      case PointerShape(const, addressSpace) =>
        OpenCL.AST.VarDecl(
          flattened.leafName(leaf.path),
          OpenCL.AST.PointerType(addressSpace, leaf.t, const),
          AddressSpace.Private,
          init
        )
    }

  private def collectDeclaredNames(body: Seq[Stmt]): Set[String] = {
    val names = scala.collection.mutable.Set.empty[String]
    body.foreach(collectDeclaredNames(_, names))
    names.toSet
  }

  private def collectDeclaredNames(
      stmt: Stmt,
      names: scala.collection.mutable.Set[String]
    ): Unit =
    stmt match {
      case Block(body) =>
        body.foreach(collectDeclaredNames(_, names))
      case Stmts(a, b) =>
        collectDeclaredNames(a, names)
        collectDeclaredNames(b, names)
      case ForLoop(init, _, _, body) =>
        collectDeclaredNames(init, names)
        collectDeclaredNames(body, names)
      case WhileLoop(_, body) =>
        collectDeclaredNames(body, names)
      case IfThenElse(_, trueBody, falseBody) =>
        collectDeclaredNames(trueBody, names)
        falseBody.foreach(collectDeclaredNames(_, names))
      case DeclStmt(VarDecl(name, _, _)) =>
        names += name
      case _ =>
    }

  private def leaves(t: Type): Option[Seq[Leaf]] = {
    def loop(current: Type, path: List[String]): Option[Seq[Leaf]] =
      current match {
        case st: C.AST.StructType if st.fields.nonEmpty =>
          val nested = st.fields.map { case (fieldType, fieldName) =>
            loop(fieldType, path :+ fieldName)
          }
          if (nested.forall(_.isDefined)) Some(nested.flatten(_.get)) else None
        case _: C.AST.ArrayType | _: C.AST.PointerType =>
          None
        case other =>
          Some(Seq(Leaf(path, other)))
      }

    loop(t, Nil).filter(_.forall(_.path.nonEmpty))
  }

  private def validUses(stmts: Seq[Stmt], name: String, flattened: Flattened): Boolean = {
    val allowedPaths = flattened.leaves.map(_.path).toSet
    val uses = scala.collection.mutable.ArrayBuffer.empty[Option[List[String]]]

    stmts.foreach {
      case DeclStmt(VarDecl(`name`, _, _)) =>
      case stmt =>
        collectUses(stmt, name, uses)
    }

    uses.nonEmpty && uses.forall {
      case Some(path) => allowedPaths(path)
      case None => false
    }
  }

  private def collectUses(
      node: Node,
      name: String,
      out: scala.collection.mutable.ArrayBuffer[Option[List[String]]]
    ): Unit =
    node match {
      case expr: Expr =>
        fieldPath(expr) match {
          case Some((`name`, path)) =>
            out += Some(path)
          case Some(_) =>
            visitExprChildren(expr, name, out)
          case None =>
            expr match {
              case DeclRef(`name`) =>
                out += None
              case _ =>
                visitExprChildren(expr, name, out)
            }
        }

      case Block(body) =>
        body.foreach(collectUses(_, name, out))
      case Stmts(a, b) =>
        collectUses(a, name, out)
        collectUses(b, name, out)
      case ForLoop(init, cond, increment, body) =>
        collectUses(init, name, out)
        collectUses(cond, name, out)
        collectUses(increment, name, out)
        collectUses(body, name, out)
      case WhileLoop(cond, body) =>
        collectUses(cond, name, out)
        collectUses(body, name, out)
      case IfThenElse(cond, trueBody, falseBody) =>
        collectUses(cond, name, out)
        collectUses(trueBody, name, out)
        falseBody.foreach(collectUses(_, name, out))
      case DeclStmt(VarDecl(_, _, init)) =>
        init.foreach(collectUses(_, name, out))
      case ExprStmt(expr) =>
        collectUses(expr, name, out)
      case _ =>
    }

  private def visitExprChildren(
      expr: Expr,
      name: String,
      out: scala.collection.mutable.ArrayBuffer[Option[List[String]]]
    ): Unit =
    expr match {
      case Assignment(lhs, rhs) =>
        collectUses(lhs, name, out)
        collectUses(rhs, name, out)
      case FunCall(fun, args) =>
        collectUses(fun, name, out)
        args.foreach(collectUses(_, name, out))
      case ArraySubscript(array, index) =>
        collectUses(array, name, out)
        collectUses(index, name, out)
      case UnaryExpr(_, e) =>
        collectUses(e, name, out)
      case BinaryExpr(lhs, _, rhs) =>
        collectUses(lhs, name, out)
        collectUses(rhs, name, out)
      case TernaryExpr(cond, thenE, elseE) =>
        collectUses(cond, name, out)
        collectUses(thenE, name, out)
        collectUses(elseE, name, out)
      case Cast(_, e) =>
        collectUses(e, name, out)
      case ArrayLiteral(_, values) =>
        values.foreach(collectUses(_, name, out))
      case RecordLiteral(_, fst, snd) =>
        collectUses(fst, name, out)
        collectUses(snd, name, out)
      case _ =>
    }

  private def rewriteExpr(expr: Expr, env: Map[String, Flattened]): Expr =
    accessPath(expr) match {
      case Some((root, Some(index), path)) if env.contains(root) && path.nonEmpty =>
        ArraySubscript(DeclRef(env(root).leafName(path)), rewriteExpr(index, env))
      case Some((root, None, path)) if env.contains(root) && path.nonEmpty =>
        DeclRef(env(root).leafName(path))
      case _ =>
        expr match {
          case Assignment(lhs, rhs) =>
            Assignment(rewriteExpr(lhs, env), rewriteExpr(rhs, env))
          case FunCall(fun, args) =>
            FunCall(fun, args.map(rewriteExpr(_, env)))
          case ArraySubscript(array, index) =>
            ArraySubscript(rewriteExpr(array, env), rewriteExpr(index, env))
          case StructMemberAccess(struct, member) =>
            StructMemberAccess(rewriteExpr(struct, env), member)
          case UnaryExpr(op, e) =>
            UnaryExpr(op, rewriteExpr(e, env))
          case BinaryExpr(lhs, op, rhs) =>
            BinaryExpr(rewriteExpr(lhs, env), op, rewriteExpr(rhs, env))
          case TernaryExpr(cond, thenE, elseE) =>
            TernaryExpr(
              rewriteExpr(cond, env),
              rewriteExpr(thenE, env),
              rewriteExpr(elseE, env)
            )
          case Cast(t, e) =>
            Cast(t, rewriteExpr(e, env))
          case ArrayLiteral(t, values) =>
            ArrayLiteral(t, values.map(rewriteExpr(_, env)))
          case RecordLiteral(t, fst, snd) =>
            RecordLiteral(t, rewriteExpr(fst, env), rewriteExpr(snd, env))
          case other =>
            other
        }
    }

  private def rewriteExprForLeaf(
      expr: Expr,
      path: List[String],
      env: Map[String, Flattened]
    ): Expr =
    expr match {
      case DeclRef(root) if env.contains(root) =>
        DeclRef(env(root).leafName(path))
      case ArraySubscript(DeclRef(root), index) if env.contains(root) =>
        ArraySubscript(DeclRef(env(root).leafName(path)), rewriteExpr(index, env))
      case ArraySubscript(array, index) =>
        ArraySubscript(rewriteExprForLeaf(array, path, env), rewriteExpr(index, env))
      case UnaryExpr(op, e) =>
        UnaryExpr(op, rewriteExprForLeaf(e, path, env))
      case TernaryExpr(cond, thenE, elseE) =>
        TernaryExpr(
          rewriteExpr(cond, env),
          rewriteExprForLeaf(thenE, path, env),
          rewriteExprForLeaf(elseE, path, env)
        )
      case Literal(text) =>
        Literal(replaceRootNames(text, path, env))
      case Cast(t, e) =>
        Cast(t, rewriteExprForLeaf(e, path, env))
      case other =>
        rewriteExpr(other, env)
    }

  private def rewriteExprForLeafWithTextFallback(
      expr: Expr,
      path: List[String],
      env: Map[String, Flattened]
    ): Expr = {
    val direct = replaceRootNames(C.AST.Printer(expr), path, env)
    if (direct != C.AST.Printer(expr)) {
      return Literal(direct)
    }
    val rewritten = rewriteExprForLeaf(expr, path, env)
    val rendered = C.AST.Printer(rewritten)
    val replaced = replaceRootNames(rendered, path, env)
    if (replaced != rendered) {
      Literal(replaced)
    } else {
      val suffixed = appendLeafSuffixToAddressOfZero(rendered, path)
      if (suffixed == rendered) rewritten else Literal(suffixed)
    }
  }

  private def appendLeafSuffixToAddressOfZero(text: String, path: List[String]): String = {
    if (path.isEmpty) {
      text
    } else {
      val suffix = path.map {
        case "_fst" => "fst"
        case "_snd" => "snd"
        case other => other.stripPrefix("_")
      }.mkString("_", "_", "")
      "(&?)([A-Za-z_][A-Za-z0-9_]*)(\\[0\\])".r.replaceAllIn(text, m => {
        val amp = m.group(1)
        val name = m.group(2)
        val index = m.group(3)
        val leafName = if (name.endsWith(suffix)) name else name + suffix
        s"$amp$leafName$index"
      })
    }
  }

  private def replaceRootNames(
      text: String,
      path: List[String],
      env: Map[String, Flattened]
    ): String =
    env.toSeq
      .sortBy { case (root, _) => -root.length }
      .foldLeft(text) { case (current, (root, flattened)) =>
        java.util.regex.Pattern
          .compile(s"(?<![A-Za-z0-9_])${java.util.regex.Pattern.quote(root)}(?![A-Za-z0-9_])")
          .matcher(current)
          .replaceAll(java.util.regex.Matcher.quoteReplacement(flattened.leafName(path)))
      }

  private def fieldPath(expr: Expr): Option[(String, List[String])] =
    accessPath(expr).collect { case (root, None, path) => root -> path }

  private def accessPath(expr: Expr): Option[(String, Option[Expr], List[String])] =
    expr match {
      case DeclRef(name) =>
        Some((name, None, Nil))
      case ArraySubscript(DeclRef(name), index) =>
        Some((name, Some(index), Nil))
      case StructMemberAccess(struct, DeclRef(member)) =>
        accessPath(struct).map { case (root, index, path) => (root, index, path :+ member) }
      case _ =>
        None
    }
}
