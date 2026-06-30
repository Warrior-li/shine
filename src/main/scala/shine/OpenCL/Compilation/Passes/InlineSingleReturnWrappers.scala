package shine.OpenCL.Compilation.Passes

import java.util.regex.{Matcher, Pattern}

import shine.C
import shine.C.AST._

/** Inline small foreign-function wrappers emitted as one-line returns.
  *
  * RISE `foreignFun` definitions often lower to tiny helper functions such as
  * `{ return fmax(x, ...); }`.  Keeping those helpers in OpenCL kernels adds
  * declarations and repeated calls even though the wrapper has no state.  This
  * pass is intentionally syntax-level: it only inlines functions whose body is
  * exactly a single return expression and leaves all other declarations intact.
  */
object InlineSingleReturnWrappers {
  private val ReturnExpr = """(?s)^\s*\{\s*return\s+([^;{}]+);\s*\}\s*$""".r
  private val MaxInlineChars = 256

  private case class Wrapper(params: Seq[String], expr: String)

  def inline(decls: Seq[Decl], body: Stmt): (Seq[Decl], Stmt) = {
    val wrappers = decls.collect {
      case FunDecl(name, _, params, Code(ReturnExpr(expr)))
          if expr.length <= MaxInlineChars =>
        name -> Wrapper(params.map(_.name), expr.trim)
    }.toMap
    if (wrappers.isEmpty) {
      decls -> body
    } else {
      val rewritten = rewriteStmt(body, wrappers)
      val remaining = decls.filterNot(d => wrappers.contains(d.name))
      remaining -> rewritten
    }
  }

  private def rewriteStmt(stmt: Stmt, wrappers: Map[String, Wrapper]): Stmt =
    Nodes.VisitAndRebuild(stmt, new Nodes.VisitAndRebuild.Visitor {
      override def post(n: Node): Node =
        n match {
          case FunCall(DeclRef(name), args) =>
            wrappers.get(name) match {
              case Some(wrapper) if wrapper.params.length == args.length =>
                Literal(inlineExpr(wrapper, args))
              case _ =>
                n
            }
          case _ =>
            n
        }
    })

  private def inlineExpr(wrapper: Wrapper, args: Seq[Expr]): String = {
    val renderedArgs = args.map(arg => s"(${C.AST.Printer(arg)})")
    val substituted = wrapper.params.zip(renderedArgs).foldLeft(wrapper.expr) {
      case (expr, (param, arg)) =>
        Pattern.compile(s"\\b${Pattern.quote(param)}\\b")
          .matcher(expr)
          .replaceAll(Matcher.quoteReplacement(arg))
    }
    s"($substituted)"
  }
}
