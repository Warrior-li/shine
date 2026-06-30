package shine.OpenCL.Compilation.Passes

import arithexpr.arithmetic.Cst
import java.util.regex.{Matcher, Pattern}
import rise.core.types.AddressSpace
import shine.C
import shine.C.AST._
import shine.OpenCL

/**
 * Pack flattened local struct leaf arrays back into one local array.
 *
 * FlattenPrivateStructs deliberately lowers local `struct` arrays to leaf
 * arrays such as `x_fst[8]` and `x_snd[8]`.  That avoids OpenCL struct-local
 * ABI issues, but leaves verbose declarations.  When all leaves have the same
 * local array shape, use one flat local array and rewrite leaf accesses to
 * affine offsets.  This preserves the flattened vec16 representation while
 * reducing declaration and ABI noise.
 */
object PackFlattenedLocalArrays {
  private case class Group(root: String, elemType: Type, size: arithexpr.arithmetic.ArithExpr, names: Seq[String]) {
    val offsets: Map[String, Int] =
      names.zipWithIndex.toMap
  }

  private def withInit(decl: VarDecl, init: Option[Expr]): VarDecl =
    decl match {
      case ov: OpenCL.AST.VarDecl =>
        OpenCL.AST.VarDecl(ov.name, ov.t, ov.addressSpace, init)
      case v =>
        VarDecl(v.name, v.t, init)
    }

  def pack(body: Stmt): Stmt =
    rewriteStmt(body, Map.empty)

  private def rewriteStmt(stmt: Stmt, env: Map[String, (String, Int, arithexpr.arithmetic.ArithExpr)]): Stmt =
    stmt match {
      case Block(body) =>
        val groups = groupsIn(body)
        val localEnv = env ++ groups.values.flatMap(g =>
          g.offsets.map { case (name, offset) => name -> (g.root, offset, g.size) })
        val rewritten = body.flatMap {
          case DeclStmt(OpenCL.AST.VarDecl(name, C.AST.ArrayType(_, _, _), AddressSpace.Local, None))
              if localEnv.contains(name) =>
            if (groups.get(localEnv(name)._1).exists(_.names.head == name)) {
              val g = groups(localEnv(name)._1)
              Seq(DeclStmt(OpenCL.AST.VarDecl(
                g.root,
                C.AST.ArrayType(g.elemType, Some(g.size * Cst(g.names.length))),
                AddressSpace.Local,
                None)))
            } else {
              Seq.empty
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
          rewriteStmt(body, env).asInstanceOf[Block])

      case WhileLoop(cond, body) =>
        WhileLoop(rewriteExpr(cond, env), rewriteStmt(body, env))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(
          rewriteExpr(cond, env),
          rewriteStmt(trueBody, env),
          falseBody.map(rewriteStmt(_, env)))

      case DeclStmt(v: OpenCL.AST.VarDecl) =>
        DeclStmt(withInit(v, v.init.map(rewriteExpr(_, env))))

      case DeclStmt(v @ VarDecl(_, _, init)) =>
        DeclStmt(withInit(v, init.map(rewriteExpr(_, env))))

      case ExprStmt(Assignment(lhs, rhs)) =>
        ExprStmt(Assignment(rewriteExpr(lhs, env), rewriteExpr(rhs, env)))

      case ExprStmt(expr) =>
        ExprStmt(rewriteExpr(expr, env))

      case other =>
        other
    }

  private def groupsIn(body: Seq[Stmt]): Map[String, Group] = {
    val namesInBlock = body.collect { case DeclStmt(VarDecl(name, _, _)) => name }.toSet
    val nonZeroOrDynamicIndexedNames =
      body.flatMap(nonZeroOrDynamicIndexedArrayNames).toSet
    body.collect {
      case DeclStmt(OpenCL.AST.VarDecl(name, C.AST.ArrayType(elemT, Some(size), _), AddressSpace.Local, None)) =>
        splitLeafName(name)
          .filterNot(namesInBlock)
          .map(root => (root, elemT, size, name))
    }.flatten
      .groupBy(_._1)
      .flatMap { case (root, entries) =>
        val sameShape = entries.map(e => (e._2, e._3)).distinct
        val hasUnsafeSingletonUse =
          entries.exists(e => e._3 == Cst(1) && nonZeroOrDynamicIndexedNames.contains(e._4))
        if (entries.size >= 2 && sameShape.size == 1 && !hasUnsafeSingletonUse) {
          val (elemT, size) = sameShape.head
          Some(root -> Group(root, elemT, size, entries.map(_._4)))
        } else {
          None
        }
      }
  }

  private def nonZeroOrDynamicIndexedArrayNames(stmt: Stmt): Seq[String] =
    stmt match {
      case Block(body) =>
        body.flatMap(nonZeroOrDynamicIndexedArrayNames)
      case Stmts(a, b) =>
        nonZeroOrDynamicIndexedArrayNames(a) ++ nonZeroOrDynamicIndexedArrayNames(b)
      case ForLoop(init, cond, increment, body) =>
        nonZeroOrDynamicIndexedArrayNames(init) ++
          nonZeroOrDynamicIndexedArrayNames(body) ++
          nonZeroOrDynamicIndexedArrayNames(ExprStmt(cond)) ++
          nonZeroOrDynamicIndexedArrayNames(ExprStmt(increment))
      case WhileLoop(cond, body) =>
        nonZeroOrDynamicIndexedArrayNames(ExprStmt(cond)) ++ nonZeroOrDynamicIndexedArrayNames(body)
      case IfThenElse(cond, trueBody, falseBody) =>
        nonZeroOrDynamicIndexedArrayNames(ExprStmt(cond)) ++
          nonZeroOrDynamicIndexedArrayNames(trueBody) ++
          falseBody.toSeq.flatMap(nonZeroOrDynamicIndexedArrayNames)
      case DeclStmt(v: OpenCL.AST.VarDecl) =>
        v.init.toSeq.flatMap(nonZeroOrDynamicIndexedArrayNames)
      case DeclStmt(v: VarDecl) =>
        v.init.toSeq.flatMap(nonZeroOrDynamicIndexedArrayNames)
      case DeclStmt(_) =>
        Seq.empty
      case ExprStmt(expr) =>
        nonZeroOrDynamicIndexedArrayNames(expr)
      case _ =>
        Seq.empty
    }

  private def nonZeroOrDynamicIndexedArrayNames(expr: Expr): Seq[String] =
    expr match {
      case ArraySubscript(DeclRef(name), index) =>
        val nested = nonZeroOrDynamicIndexedArrayNames(index)
        if (isZeroIndex(index)) nested else name +: nested
      case ArraySubscript(array, index) =>
        nonZeroOrDynamicIndexedArrayNames(array) ++ nonZeroOrDynamicIndexedArrayNames(index)
      case Assignment(lhs, rhs) =>
        nonZeroOrDynamicIndexedArrayNames(lhs) ++ nonZeroOrDynamicIndexedArrayNames(rhs)
      case UnaryExpr(_, e) =>
        nonZeroOrDynamicIndexedArrayNames(e)
      case BinaryExpr(lhs, _, rhs) =>
        nonZeroOrDynamicIndexedArrayNames(lhs) ++ nonZeroOrDynamicIndexedArrayNames(rhs)
      case TernaryExpr(c, t, f) =>
        nonZeroOrDynamicIndexedArrayNames(c) ++ nonZeroOrDynamicIndexedArrayNames(t) ++ nonZeroOrDynamicIndexedArrayNames(f)
      case FunCall(_, args) =>
        args.flatMap(nonZeroOrDynamicIndexedArrayNames)
      case Cast(_, e) =>
        nonZeroOrDynamicIndexedArrayNames(e)
      case StructMemberAccess(e, _) =>
        nonZeroOrDynamicIndexedArrayNames(e)
      case _ =>
        Seq.empty
    }

  private def isZeroIndex(index: Expr): Boolean =
    index match {
      case Literal(text) => text.trim == "0"
      case ArithmeticExpr(Cst(0)) => true
      case Cast(_, e) => isZeroIndex(e)
      case _ => false
    }

  private def splitLeafName(name: String): Option[String] = {
    def loop(current: String, stripped: Boolean): Option[String] =
      if (current.endsWith("_fst")) {
        loop(current.stripSuffix("_fst"), stripped = true)
      } else if (current.endsWith("_snd")) {
        loop(current.stripSuffix("_snd"), stripped = true)
      } else if (stripped && current.nonEmpty) {
        Some(current)
      } else {
        None
      }
    loop(name, stripped = false)
  }

  private def rewriteExpr(expr: Expr, env: Map[String, (String, Int, arithexpr.arithmetic.ArithExpr)]): Expr =
    expr match {
      case Assignment(lhs, rhs) =>
        Assignment(rewriteExpr(lhs, env), rewriteExpr(rhs, env))

      case ArraySubscript(DeclRef(name), index) if env.contains(name) =>
        val (root, offset, size) = env(name)
        ArraySubscript(DeclRef(root), addOffset(rewriteExpr(index, env), offset, size))

      case DeclRef(name) if env.contains(name) =>
        val (root, offset, size) = env(name)
        UnaryExpr(UnaryOperator.&, ArraySubscript(DeclRef(root), addOffset(Literal("0"), offset, size)))

      case UnaryExpr(op, e) =>
        UnaryExpr(op, rewriteExpr(e, env))

      case BinaryExpr(lhs, op, rhs) =>
        BinaryExpr(rewriteExpr(lhs, env), op, rewriteExpr(rhs, env))

      case TernaryExpr(c, t, f) =>
        TernaryExpr(rewriteExpr(c, env), rewriteExpr(t, env), rewriteExpr(f, env))

      case FunCall(fun, args) =>
        FunCall(fun, args.map(rewriteExpr(_, env)))

      case Cast(t, e) =>
        Cast(t, rewriteExpr(e, env))

      case StructMemberAccess(e, field) =>
        StructMemberAccess(rewriteExpr(e, env), field)

      case Literal(text) =>
        rewriteLiteral(text, env).getOrElse(Literal(rewriteLiteralTokens(text, env)))

      case other =>
        other
    }

  private def rewriteLiteral(
      text: String,
      env: Map[String, (String, Int, arithexpr.arithmetic.ArithExpr)]
    ): Option[Expr] = {
    env.get(text).map { case (root, offset, size) =>
      pointerToPackedArray(root, offset, size)
    }.orElse {
      env.collectFirst {
        case (name, (root, offset, size)) if text == s"&$name[0]" =>
          pointerToPackedArray(root, offset, size)
      }
    }
  }

  private def pointerToPackedArray(
      root: String,
      offset: Int,
      size: arithexpr.arithmetic.ArithExpr
    ): Expr =
    if (offset == 0) DeclRef(root)
    else UnaryExpr(UnaryOperator.&, ArraySubscript(DeclRef(root), packedOffset(offset, size)))

  private def rewriteLiteralTokens(
      text: String,
      env: Map[String, (String, Int, arithexpr.arithmetic.ArithExpr)]
    ): String =
    env.keys.toSeq.sortBy(-_.length).foldLeft(text) { (current, name) =>
      val (root, offset, size) = env(name)
      val pattern = raw"(?<![A-Za-z0-9_])${Pattern.quote(name)}(?![A-Za-z0-9_])".r
      pattern.replaceAllIn(current, Matcher.quoteReplacement(pointerText(root, offset, size)))
    }

  private def pointerText(
      root: String,
      offset: Int,
      size: arithexpr.arithmetic.ArithExpr
    ): String =
    if (offset == 0) root else s"&$root[${(size * Cst(offset)).toString}]"

  private def addOffset(index: Expr, offset: Int, size: arithexpr.arithmetic.ArithExpr): Expr =
    if (offset == 0) {
      index
    } else if (isZeroIndex(index)) {
      packedOffset(offset, size)
    } else {
      BinaryExpr(packedOffset(offset, size), BinaryOperator.+, index)
    }

  private def packedOffset(offset: Int, size: arithexpr.arithmetic.ArithExpr): Expr =
    ArithmeticExpr(size * Cst(offset))
}
