package shine.OpenCL.Compilation.Passes

import rise.core.types.AddressSpace
import shine.C
import shine.C.AST._
import shine.OpenCL

/**
 * Normalize local-memory barriers around hoisted local buffers.
 *
 * Earlier DPIA-level passes insert barriers conservatively before local
 * allocation hoisting and kernel parameter adaptation.  At this stage the
 * OpenCL AST exposes the actual local parameters and local declarations.  We
 * therefore also repair missing barriers around local write/read dependencies
 * that were obscured by higher-level expression lowering, and remove barriers
 * that are only attached to map/workgroup shells or adjacent local writes.
 * Loop bodies are handled conservatively: trailing barriers are inserted when a
 * loop both reads and writes the same local buffer, because the next iteration
 * may overwrite data that previous work-items are still reading.
 */
object PruneRedundantLocalBarriers {
  private case class Effects(reads: Set[String] = Set.empty, writes: Set[String] = Set.empty) {
    def ++(other: Effects): Effects =
      Effects(reads ++ other.reads, writes ++ other.writes)

    def touchesLocal: Boolean =
      reads.nonEmpty || writes.nonEmpty

    def needsBarrierBefore(next: Effects): Boolean =
      writes.exists(next.reads.contains) || reads.exists(next.writes.contains)

    def hasLoopCarriedLocalReuse: Boolean =
      reads.exists(writes.contains)
  }

  def prune(params: Seq[ParamDecl])(body: Stmt): Stmt = {
    val localParamNames = params.collect {
      case ParamDecl(name, OpenCL.AST.PointerType(AddressSpace.Local, _, _)) => name
    }.toSet
    val localNames = localParamNames ++ collectLocalDecls(body)

    if (localNames.isEmpty) body else rewriteStmt(body, localNames, inLoop = false)
  }

  private def collectLocalDecls(stmt: Stmt): Set[String] = {
    var names = Set.empty[String]
    Nodes.VisitAndRebuild(stmt, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result = {
        n match {
          case DeclStmt(OpenCL.AST.VarDecl(name, _, AddressSpace.Local, _)) =>
            names += name
          case DeclStmt(OpenCL.AST.VarDecl(name, OpenCL.AST.PointerType(AddressSpace.Local, _, _), _, _)) =>
            names += name
          case _ =>
        }
        Continue(n, this)
      }
    })
    names
  }

  private def rewriteStmt(stmt: Stmt, localNames: Set[String], inLoop: Boolean): Stmt =
    stmt match {
      case Block(body) =>
        Block(pruneSequence(body.map(rewriteStmt(_, localNames, inLoop)), localNames, inLoop))

      case Stmts(a, b) =>
        val stmts = flatten(Stmts(
          rewriteStmt(a, localNames, inLoop),
          rewriteStmt(b, localNames, inLoop)
        ))
        blockOrStmt(pruneSequence(stmts, localNames, inLoop))

      case ForLoop(init, cond, increment, body) =>
        val rewrittenBody = rewriteStmt(body, localNames, inLoop = true).asInstanceOf[Block]
        val initDecl = init.asInstanceOf[DeclStmt]
        if (isLocalIdStridedLoop(initDecl, increment)) {
          val hadLocalBarrier = containsLocalBarrier(rewrittenBody)
          val loop = ForLoop(initDecl, cond, increment, removeLocalBarriers(rewrittenBody).asInstanceOf[Block])
          val writesLocal = stmtEffects(rewrittenBody, localNames).writes.nonEmpty
          if (hadLocalBarrier || writesLocal) Block(Seq(loop, localBarrier)) else loop
        } else {
          ForLoop(initDecl, cond, increment, withLoopCarriedBarrier(rewrittenBody, localNames))
        }

      case WhileLoop(cond, body) =>
        WhileLoop(cond, rewriteStmt(body, localNames, inLoop = true))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(
          cond,
          rewriteStmt(trueBody, localNames, inLoop),
          falseBody.map(rewriteStmt(_, localNames, inLoop))
        )

      case other =>
        other
    }

  private def pruneSequence(stmts: Seq[Stmt], localNames: Set[String], inLoop: Boolean): Seq[Stmt] = {
    val flat = stmts.flatMap(flatten)
    val out = scala.collection.mutable.ArrayBuffer.empty[Stmt]
    var sinceBarrier = Effects()

    flat.zipWithIndex.foreach { case (stmt, i) =>
      if (isLocalBarrier(stmt)) {
        val before = sinceBarrier
        val after = effectsUntilNextBarrier(flat.drop(i + 1), localNames)

        if (before.needsBarrierBefore(after)) {
          if (!out.lastOption.exists(isLocalBarrier)) {
            out += stmt
          }
        }
        sinceBarrier = Effects()
      } else {
        val effects = stmtExposedEffects(stmt, localNames)
        if (sinceBarrier.needsBarrierBefore(effects) && !out.lastOption.exists(isLocalBarrier)) {
          out += localBarrier
          sinceBarrier = Effects()
        }
        out += stmt
        sinceBarrier = sinceBarrier ++ effects
      }
    }

    out.toSeq
  }

  private def withLoopCarriedBarrier(body: Block, localNames: Set[String]): Block = {
    val effects = stmtEffects(body, localNames)
    val tailEffects = effectsAfterLastBarrier(body.body, localNames)
    val nextIterationPrefix = effectsBeforeFirstBarrier(body.body, localNames)
    if (
      (effects.hasLoopCarriedLocalReuse ||
        (effects.reads.nonEmpty && effects.writes.nonEmpty)) &&
        tailEffects.needsBarrierBefore(nextIterationPrefix) &&
        !body.body.lastOption.exists(isLocalBarrier)
    ) {
      Block(body.body :+ localBarrier)
    } else {
      body
    }
  }

  private def effectsAfterLastBarrier(stmts: Seq[Stmt], localNames: Set[String]): Effects = {
    var effects = Effects()
    stmts.flatMap(flatten).foreach { stmt =>
      if (isLocalBarrier(stmt)) {
        effects = Effects()
      } else {
        effects = effects ++ stmtExposedEffects(stmt, localNames)
      }
    }
    effects
  }

  private def effectsUntilNextBarrier(stmts: Seq[Stmt], localNames: Set[String]): Effects = {
    var effects = Effects()
    val iter = stmts.iterator
    var done = false
    while (iter.hasNext && !done) {
      val stmt = iter.next()
      if (isLocalBarrier(stmt)) {
        done = true
      } else {
        effects = effects ++ stmtExposedEffects(stmt, localNames)
      }
    }
    effects
  }

  private def effectsBeforeFirstBarrier(stmts: Seq[Stmt], localNames: Set[String]): Effects =
    effectsUntilNextBarrier(stmts, localNames)

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

  private def isLocalBarrier(stmt: Stmt): Boolean =
    stmt match {
      case OpenCL.AST.Barrier(true, false) => true
      case _ => false
    }

  private def containsLocalBarrier(stmt: Stmt): Boolean =
    stmt match {
      case s if isLocalBarrier(s) => true
      case Block(body) => body.exists(containsLocalBarrier)
      case Stmts(a, b) => containsLocalBarrier(a) || containsLocalBarrier(b)
      case ForLoop(_, _, _, body) => containsLocalBarrier(body)
      case WhileLoop(_, body) => containsLocalBarrier(body)
      case IfThenElse(_, trueBody, falseBody) =>
        containsLocalBarrier(trueBody) || falseBody.exists(containsLocalBarrier)
      case _ => false
    }

  private def removeLocalBarriers(stmt: Stmt): Stmt =
    stmt match {
      case s if isLocalBarrier(s) => Block(Seq.empty)
      case Block(body) => Block(body.flatMap(s => flatten(removeLocalBarriers(s))))
      case Stmts(a, b) => blockOrStmt(flatten(removeLocalBarriers(a)) ++ flatten(removeLocalBarriers(b)))
      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment, removeLocalBarriers(body).asInstanceOf[Block])
      case WhileLoop(cond, body) => WhileLoop(cond, removeLocalBarriers(body))
      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, removeLocalBarriers(trueBody), falseBody.map(removeLocalBarriers))
      case other => other
    }

  private def localBarrier: Stmt =
    OpenCL.AST.Barrier(local = true, global = false)

  private def isLocalIdStridedLoop(init: DeclStmt, increment: Expr): Boolean = {
    val (loopName, startsAtLocalId) = init match {
      case DeclStmt(VarDecl(name, _, Some(expr))) => name -> containsOpenCLCall(expr, "get_local_id")
      case DeclStmt(VarDecl(name, _, None)) => name -> false
      case _ => "" -> false
    }
    startsAtLocalId && (
      containsOpenCLCall(increment, "get_local_size") ||
        referencesName(increment, loopName)
    )
  }

  private def containsOpenCLCall(expr: Expr, name: String): Boolean = {
    var found = false
    Nodes.VisitAndRebuild(expr, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result = {
        n match {
          case FunCall(DeclRef(`name`), _) =>
            found = true
            Stop(n)
          case ArithmeticExpr(ae) if ae.toString.startsWith(s"$name(") =>
            found = true
            Stop(n)
          case Literal(text) if text.startsWith(s"$name(") =>
            found = true
            Stop(n)
          case _ =>
            Continue(n, this)
        }
      }
    })
    found
  }

  private def referencesName(expr: Expr, name: String): Boolean = {
    var found = false
    Nodes.VisitAndRebuild(expr, new Nodes.VisitAndRebuild.Visitor {
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

  private def stmtEffects(stmt: Stmt, localNames: Set[String]): Effects =
    stmt match {
      case Block(body) =>
        body.foldLeft(Effects())(_ ++ stmtEffects(_, localNames))
      case Stmts(a, b) =>
        stmtEffects(a, localNames) ++ stmtEffects(b, localNames)
      case DeclStmt(VarDecl(_, _, init)) =>
        init.map(exprReads(_, localNames)).getOrElse(Effects())
      case ExprStmt(Assignment(lhs, rhs)) =>
        lvalueEffects(lhs, localNames) ++ exprReads(rhs, localNames)
      case ExprStmt(expr) =>
        exprReads(expr, localNames)
      case ForLoop(init, cond, increment, body) =>
        stmtEffects(init, localNames) ++
          exprReads(cond, localNames) ++
          exprReads(increment, localNames) ++
          stmtEffects(body, localNames)
      case WhileLoop(cond, body) =>
        exprReads(cond, localNames) ++ stmtEffects(body, localNames)
      case IfThenElse(cond, trueBody, falseBody) =>
        exprReads(cond, localNames) ++
          stmtEffects(trueBody, localNames) ++
          falseBody.map(stmtEffects(_, localNames)).getOrElse(Effects())
      case _ =>
        Effects()
    }

  private def stmtExposedEffects(stmt: Stmt, localNames: Set[String]): Effects =
    stmt match {
      case Block(body) =>
        effectsAfterLastBarrier(body, localNames)
      case Stmts(a, b) =>
        effectsAfterLastBarrier(flatten(Stmts(a, b)), localNames)
      case ForLoop(init, cond, increment, body) =>
        stmtEffects(init, localNames) ++
          exprReads(cond, localNames) ++
          exprReads(increment, localNames) ++
          effectsAfterLastBarrier(flatten(body), localNames)
      case WhileLoop(cond, body) =>
        exprReads(cond, localNames) ++ stmtExposedEffects(body, localNames)
      case IfThenElse(cond, trueBody, falseBody) =>
        exprReads(cond, localNames) ++
          stmtExposedEffects(trueBody, localNames) ++
          falseBody.map(stmtExposedEffects(_, localNames)).getOrElse(Effects())
      case other =>
        stmtEffects(other, localNames)
    }

  private def lvalueEffects(expr: Expr, localNames: Set[String]): Effects =
    expr match {
      case DeclRef(name) if localNames(name) =>
        Effects(writes = Set(name))
      case ArraySubscript(array, index) =>
        lvalueEffects(array, localNames) ++ exprReads(index, localNames)
      case StructMemberAccess(struct, _) =>
        lvalueEffects(struct, localNames)
      case _ =>
        exprReads(expr, localNames)
    }

  private def exprReads(expr: Expr, localNames: Set[String]): Effects = {
    var reads = Set.empty[String]
    Nodes.VisitAndRebuild(expr, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result = {
        n match {
          case DeclRef(name) if localNames(name) =>
            reads += name
          case _ =>
        }
        Continue(n, this)
      }
    })
    Effects(reads = reads)
  }
}
