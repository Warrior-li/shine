package shine.OpenCL.Compilation.Passes

import shine.C
import shine.C.AST._

/**
 * Remove redundant private array copies in generated kernel bodies.
 *
 * A common destination-passing artifact is:
 *
 *   T dst[N];
 *   ...
 *   for (...) dst[index] = src[index];
 *   for (...) use(dst[index]);
 *
 * If `dst` is only a full copy of `src`, and neither array is written after
 * the copy, later reads of `dst` can safely read `src` directly.  This pass is
 * deliberately conservative and does not unroll loops or scalarize arrays.
 */
object EliminatePrivateArrayCopies {
  private case class FieldCopyRun(
      dst: String,
      src: String,
      paths: Set[List[String]],
      endIndex: Int
    )

  def eliminate(body: Stmt): Stmt =
    rewriteStmt(body, allowEliminate = true)

  private def rewriteStmt(stmt: Stmt, allowEliminate: Boolean): Stmt =
    stmt match {
      case Block(body) =>
        val rewritten = body.map(rewriteStmt(_, allowEliminate))
        if (allowEliminate) {
          val (body2, eliminated) = eliminateCopies(rewritten)
          Block(removeEliminatedDecls(body2, eliminated))
        } else {
          Block(rewritten)
        }

      case Stmts(a, b) =>
        val rewritten = flatten(Stmts(
          rewriteStmt(a, allowEliminate),
          rewriteStmt(b, allowEliminate)
        ))
        if (allowEliminate) {
          val (body2, eliminated) = eliminateCopies(rewritten)
          blockOrStmt(removeEliminatedDecls(body2, eliminated))
        } else {
          blockOrStmt(rewritten)
        }

      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
          rewriteStmt(body, allowEliminate = false).asInstanceOf[Block])

      case WhileLoop(cond, body) =>
        WhileLoop(cond, rewriteStmt(body, allowEliminate = false))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond,
          rewriteStmt(trueBody, allowEliminate),
          falseBody.map(rewriteStmt(_, allowEliminate)))

      case other =>
        other
    }

  private def eliminateCopies(stmts: Seq[Stmt]): (Seq[Stmt], Set[String]) = {
    val out = scala.collection.mutable.ArrayBuffer.empty[Stmt]
    var eliminated = Set.empty[String]
    var i = 0

    while (i < stmts.length) {
      fieldCopyRun(stmts, i) match {
        case Some(FieldCopyRun(dst, src, copiedPaths, endIndex)) =>
          val tail = stmts.drop(endIndex)
          val dstReads = readFieldPaths(tail, dst)
          if (removableDeclarationOnly(out.toSeq, dst) &&
              !writesTo(tail, dst) &&
              !writesTo(tail, src) &&
              dstReads.exists(_.subsetOf(copiedPaths))) {
            val rewrittenTail = tail.map(replaceReads(_, dst, src))
            out ++= rewrittenTail
            eliminated += dst
            i = stmts.length
          } else {
            out += stmts(i)
            i += 1
          }

        case None => copyPair(stmts(i)) match {
        case Some((dst, src)) =>
          val tail = stmts.drop(i + 1)
          if (!writesTo(tail, dst) && !writesTo(tail, src)) {
            val rewrittenTail = tail.map(replaceReads(_, dst, src))
            out ++= rewrittenTail
            eliminated += dst
            i = stmts.length
          } else {
            out += stmts(i)
            i += 1
          }
        case None =>
          out += stmts(i)
          i += 1
        }
      }
    }

    (out.toSeq, eliminated)
  }

  private def fieldCopyRun(stmts: Seq[Stmt], start: Int): Option[FieldCopyRun] =
    fieldCopy(stmts(start)).flatMap { case (dst, src, firstPath) =>
      val paths = scala.collection.mutable.Set(firstPath)
      var end = start + 1
      var keepGoing = true
      while (keepGoing && end < stmts.length) {
        fieldCopy(stmts(end)) match {
          case Some((d, s, path)) if d == dst && s == src =>
            paths += path
            end += 1
          case _ =>
            keepGoing = false
        }
      }
      Some(FieldCopyRun(dst, src, paths.toSet, end))
    }

  private def fieldCopy(stmt: Stmt): Option[(String, String, List[String])] =
    stmt match {
      case Block(Seq(single)) =>
        fieldCopy(single)
      case ExprStmt(Assignment(lhs, rhs)) =>
        for {
          (dst, dstPath) <- fieldPath(lhs)
          (src, srcPath) <- fieldPath(rhs)
          if dst != src && dstPath.nonEmpty && dstPath == srcPath
        } yield (dst, src, dstPath)
      case _ =>
        None
    }

  private def copyPair(stmt: Stmt): Option[(String, String)] =
    stmt match {
      case ForLoop(_, _, _, body) =>
        copyPair(body)
      case Block(body) =>
        val meaningful = body.filterNot(isIgnorable)
        meaningful match {
          case Seq(single) => copyPair(single)
          case many if many.nonEmpty =>
            val pairs = many.flatMap(copyPair)
            if (pairs.size == many.size && pairs.distinct.size == 1) {
              pairs.headOption
            } else {
              None
            }
          case _ => None
        }
      case Stmts(a, b) =>
        val pairs = flatten(Stmts(a, b)).filterNot(isIgnorable).flatMap(copyPair)
        if (pairs.nonEmpty && pairs.distinct.size == 1) pairs.headOption else None
      case ExprStmt(Assignment(ArraySubscript(DeclRef(dst), dstIndex),
                               ArraySubscript(DeclRef(src), srcIndex)))
          if dst != src && dstIndex == srcIndex =>
        Some(dst -> src)
      case _ =>
        None
    }

  private def isIgnorable(stmt: Stmt): Boolean =
    stmt match {
      case Comment(_) => true
      case _ => false
    }

  private def removeEliminatedDecls(stmts: Seq[Stmt], eliminated: Set[String]): Seq[Stmt] =
    if (eliminated.isEmpty) {
      stmts
    } else {
      stmts.filterNot {
        case DeclStmt(VarDecl(name, _: C.AST.ArrayType, None)) if eliminated(name) => true
        case DeclStmt(VarDecl(name, _, None)) if eliminated(name) => true
        case _ => false
      }
    }

  private def replaceReads(stmt: Stmt, dst: String, src: String): Stmt =
    Nodes.VisitAndRebuild(stmt, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result = {
        n match {
          case DeclRef(name) if name == dst =>
            Stop(DeclRef(src))
          case _ =>
            Continue(n, this)
        }
      }
    })

  private def writesTo(stmts: Seq[Stmt], name: String): Boolean =
    stmts.exists(writesTo(_, name))

  private def writesTo(stmt: Stmt, name: String): Boolean = {
    var found = false
    Nodes.VisitAndRebuild(stmt, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result = {
        n match {
          case Assignment(lhs, _) if lvalueRoot(lhs).contains(name) =>
            found = true
            Stop(n)
          case _ =>
            Continue(n, this)
        }
      }
    })
    found
  }

  private def lvalueRoot(expr: Expr): Option[String] =
    expr match {
      case DeclRef(name) => Some(name)
      case ArraySubscript(array, _) => lvalueRoot(array)
      case StructMemberAccess(struct, _) => lvalueRoot(struct)
      case _ => None
    }

  private def fieldPath(expr: Expr): Option[(String, List[String])] =
    expr match {
      case DeclRef(name) =>
        Some(name -> Nil)
      case StructMemberAccess(struct, DeclRef(member)) =>
        fieldPath(struct).map { case (root, path) => root -> (path :+ member) }
      case _ =>
        None
    }

  private def readFieldPaths(stmts: Seq[Stmt], name: String): Option[Set[List[String]]] = {
    val paths = scala.collection.mutable.Set.empty[List[String]]
    var invalid = false
    stmts.foreach { stmt =>
      Nodes.VisitAndRebuild(stmt, new Nodes.VisitAndRebuild.Visitor {
        override def pre(n: Node): Result = {
          n match {
            case s: StructMemberAccess =>
              fieldPath(s) match {
                case Some((root, path)) if root == name =>
                  paths += path
                  Stop(n)
                case _ =>
                  Continue(n, this)
              }
            case DeclRef(`name`) =>
              invalid = true
              Stop(n)
            case _ =>
              Continue(n, this)
          }
        }
      })
    }
    if (invalid) None else Some(paths.toSet)
  }

  private def removableDeclarationOnly(stmts: Seq[Stmt], name: String): Boolean = {
    var foundDecl = false
    val others = stmts.filterNot {
      case DeclStmt(VarDecl(`name`, _, None)) =>
        foundDecl = true
        true
      case _ =>
        false
    }
    foundDecl && !referencesName(others, name)
  }

  private def referencesName(stmts: Seq[Stmt], name: String): Boolean =
    stmts.exists(referencesName(_, name))

  private def referencesName(stmt: Stmt, name: String): Boolean = {
    var found = false
    Nodes.VisitAndRebuild(stmt, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result = {
        n match {
          case DeclRef(`name`) =>
            found = true
            Stop(n)
          case _ =>
            Continue(n, this)
        }
      }
    })
    found
  }

  private def flatten(stmt: Stmt): Seq[Stmt] =
    stmt match {
      case Block(body) => body.flatMap(flatten)
      case Stmts(a, b) => flatten(a) ++ flatten(b)
      case other => Seq(other)
    }

  private def blockOrStmt(stmts: Seq[Stmt]): Stmt =
    stmts match {
      case Seq(single) => single
      case many => Block(many)
    }
}
