package shine.OpenCL.Compilation.Passes

import arithexpr.arithmetic.Cst
import rise.core.types.AddressSpace
import shine.{C, OpenCL}
import shine.C.AST._
import shine.OpenCL.{BuiltInFunctionCall, GlobalSize, LocalSize}

/**
 * Remove code-generation artifacts that do not affect kernel semantics.
 *
 * The C/OpenCL generator keeps internal comments and sometimes emits scalar
 * loop/index placeholders for iteration-count-one loops.  They are useful while
 * debugging lowering, but production kernels should not carry that noise.  This
 * pass is conservative: it only removes comments and unused scalar declarations
 * whose initializers are pure expressions.
 */
object CleanGeneratedKernelBody {
  private val MaxIntegerCseTempsPerStatement = 4
  private val MaxSmallLoopUnrollIterations = 8
  private val MaxMergedAccumulatorAssignments = 4
  private val MaxInlineTernaryAssignmentExprSize = 256

  private def withInit(decl: VarDecl, init: Option[Expr]): VarDecl =
    decl match {
      case v: shine.OpenCL.AST.VarDecl =>
        shine.OpenCL.AST.VarDecl(v.name, v.t, v.addressSpace, init)
      case v =>
        VarDecl(v.name, v.t, init)
    }

  def clean(body: Stmt): Stmt =
    clean(body, wgConfig = None)

  def clean(body: Stmt, wgConfig: Option[(LocalSize, GlobalSize)]): Stmt =
    clean(body, wgConfig, Seq.empty)

  def clean(
      body: Stmt,
      wgConfig: Option[(LocalSize, GlobalSize)],
      kernelParams: Seq[ParamDecl]
    ): Stmt = {
    val localNames = localMemoryNames(body, kernelParams)
    val stripped = stripComments(body)
    val unrolled = unrollSmallConstantLoops(stripped)
    val hoisted = hoistLoopInvariantPrefixes(unrolled)
    val simplified = simplifyExpressions(simplifyStatements(hoisted))
    val rangeSimplified = simplifyIntegerExpressionsWithRanges(
      simplified,
      workGroupRanges(wgConfig),
      localIdRanges(wgConfig)
    )
    val factored = factorRepeatedIntegerExprs(rangeSimplified)
    val statementSimplified = simplifyExpressions(simplifyStatements(factored))
    val valueReused = reuseIdenticalPureValueAssignments(statementSimplified)
    val queryReused = reuseIdenticalOpenCLQueryDecls(valueReused)
    val inlined = inlineSingleUseScalarDecls(queryReused)
    val mergedBlocks = mergeAdjacentPureDeclBlocks(inlined)
    val forwarded = forwardScalarAccumulatorCopies(mergedBlocks)
    val exprForwarded = forwardSingleAssignmentTemps(forwarded)
    val pruned = pruneUnusedScalarDecls(exprForwarded)
    val finalUnrolled = simplifyStatements(simplifyExpressions(
      unrollSmallConstantLoops(unrollSmallConstantLoops(pruned))))
    val finalHoisted = simplifyStatements(simplifyExpressions(
      hoistLoopInvariantPrefixes(finalUnrolled)))
    val finalValueReused = reuseIdenticalPureValueAssignments(finalHoisted)
    val lexicalIntReused = reuseKnownIntegerSubexpressions(finalValueReused)
    val ownerCollapsed = collapseSingletonLocalOwnerLoops(lexicalIntReused)
    val ownerSimplified = simplifyStatements(simplifyExpressions(
      unrollSmallConstantLoops(unrollSmallConstantLoops(ownerCollapsed))))
    val singleIterLocalLoops = collapseSingleIterationLocalIdLoops(ownerSimplified, wgConfig)
    val mergedLoops = mergeAdjacentIndependentForLoops(singleIterLocalLoops)
    val guardedBarriers = guardLoopTailLocalBarriers(mergedLoops)
    val ownerGuarded = guardLocalReductionOwners(guardedBarriers, wgConfig, localNames)
    val ownerRangeSimplified = simplifyIntegerExpressionsWithRanges(
      ownerGuarded,
      workGroupRanges(wgConfig),
      localIdRanges(wgConfig))
    val localWriteHoisted = hoistIndependentLocalWriteBarrierRuns(ownerRangeSimplified, localNames)
    val bookkeepingBarriersPruned =
      prunePrivateBookkeepingBarriers(localWriteHoisted, localNames)
    val mergedOwnerIfs = mergeAdjacentIdenticalIfs(bookkeepingBarriersPruned)
    val collapsedOwnerIfs = collapseNestedIdenticalIfs(mergedOwnerIfs)
    val mergedInitializers = mergeInitialAssignmentsIntoDecls(collapsedOwnerIfs)
    val repairedBarriers = repairLocalDependencyBarriers(mergedInitializers, localNames)
    val noTrailingWgBarriers = dropTrailingWorkGroupBarriers(repairedBarriers)
    val shrunkStaticArrays = shrinkStaticLocalArrays(noTrailingWgBarriers, wgConfig)
    val finalScalarInlined = inlineSingleUseScalarDecls(shrunkStaticArrays)
    val finalIntegerFactored = factorRepeatedIntegerExprs(finalScalarInlined)
    val finalIntegerReused = reuseKnownIntegerSubexpressions(finalIntegerFactored)
    val arraySelectEliminated = eliminateSingleUsePrivateArraySelects(finalIntegerReused)
    val finalInlined = pruneUnusedScalarDecls(
      inlineSingleUseScalarDecls(inlineLiteralIntDecls(arraySelectEliminated)))
    val splitTernaries = splitLargeTernaryAssignments(finalInlined)
    flattenTrivialBlocks(simplifyKnownBranchConditions(splitTernaries))
  }

  private case class BranchFact(value: Boolean, refs: Set[String])

  private def simplifyKnownBranchConditions(stmt: Stmt): Stmt =
    simplifyKnownBranchConditions(stmt, Map.empty)

  private def simplifyKnownBranchConditions(
      stmt: Stmt,
      facts: Map[String, BranchFact]
    ): Stmt =
    stmt match {
      case Block(body) =>
        val out = scala.collection.mutable.ArrayBuffer.empty[Stmt]
        var currentFacts = facts
        body.foreach { s =>
          val rewritten = simplifyKnownBranchConditions(s, currentFacts)
          out ++= flatten(rewritten)
          val writes = assignedNames(s)
          if (writes.nonEmpty) {
            currentFacts = currentFacts.filterNot {
              case (_, fact) => fact.refs.exists(writes.contains)
            }
          }
        }
        Block(out.toSeq)

      case Stmts(a, b) =>
        simplifyKnownBranchConditions(Block(flatten(Stmts(a, b))), facts)

      case ForLoop(init, cond, increment, body) =>
        val bodyFacts = facts -- assignedNames(init)
        val rewrittenBody = simplifyKnownBranchConditions(body, bodyFacts)
        ForLoop(
          init.asInstanceOf[DeclStmt],
          cond,
          increment,
          Block(flatten(rewrittenBody)))

      case WhileLoop(cond, body) =>
        WhileLoop(cond, simplifyKnownBranchConditions(body, facts))

      case IfThenElse(cond, trueBody, falseBody) =>
        conditionFactKey(cond).flatMap(facts.get) match {
          case Some(BranchFact(true, _)) =>
            simplifyKnownBranchConditions(trueBody, facts)
          case Some(BranchFact(false, _)) =>
            falseBody
              .map(simplifyKnownBranchConditions(_, facts))
              .getOrElse(Block(Seq.empty))
          case None =>
            val key = conditionFactKey(cond)
            val refs = collectDeclRefs(cond)
            val trueFacts =
              key.map(k => facts + (k -> BranchFact(value = true, refs)))
                .getOrElse(facts)
            val falseFacts =
              key.map(k => facts + (k -> BranchFact(value = false, refs)))
                .getOrElse(facts)
            IfThenElse(
              cond,
              simplifyKnownBranchConditions(trueBody, trueFacts),
              falseBody.map(simplifyKnownBranchConditions(_, falseFacts))
            )
        }

      case other =>
        other
    }

  private def conditionFactKey(expr: Expr): Option[String] =
    if (pure(expr)) cPrinterKey(expr) else None

  private def splitLargeTernaryAssignments(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        Block(body.map(splitLargeTernaryAssignments))

      case Stmts(a, b) =>
        blockOrStmt(flatten(Stmts(
          splitLargeTernaryAssignments(a),
          splitLargeTernaryAssignments(b)
        )))

      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
          splitLargeTernaryAssignments(body).asInstanceOf[Block])

      case WhileLoop(cond, body) =>
        WhileLoop(cond, splitLargeTernaryAssignments(body))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(
          cond,
          splitLargeTernaryAssignments(trueBody),
          falseBody.map(splitLargeTernaryAssignments)
        )

      case ExprStmt(Assignment(lhs, rhs))
          if pure(lhs) &&
             ternaryCount(rhs) > 0 &&
             exprSize(rhs) > MaxInlineTernaryAssignmentExprSize =>
        splitTernaryAssignment(lhs, rhs)

      case other =>
        other
    }

  private def splitTernaryAssignment(lhs: Expr, rhs: Expr): Stmt =
    rhs match {
      case TernaryExpr(cond, thenE, elseE) =>
        IfThenElse(
          cond,
          blockOrStmt(Seq(splitTernaryAssignment(lhs, thenE))),
          Some(blockOrStmt(Seq(splitTernaryAssignment(lhs, elseE))))
        )
      case _ =>
        ExprStmt(Assignment(lhs, rhs))
    }

  private def ternaryCount(expr: Expr): Int =
    expr match {
      case TernaryExpr(cond, thenE, elseE) =>
        1 + ternaryCount(cond) + ternaryCount(thenE) + ternaryCount(elseE)
      case BinaryExpr(lhs, _, rhs) =>
        ternaryCount(lhs) + ternaryCount(rhs)
      case UnaryExpr(_, e) =>
        ternaryCount(e)
      case ArraySubscript(array, index) =>
        ternaryCount(array) + ternaryCount(index)
      case StructMemberAccess(struct, _) =>
        ternaryCount(struct)
      case FunCall(fun, args) =>
        ternaryCount(fun) + args.map(ternaryCount).sum
      case Cast(_, e) =>
        ternaryCount(e)
      case shine.OpenCL.AST.VectorLiteral(_, values) =>
        values.map(ternaryCount).sum
      case _ =>
        0
    }

  private def eliminateSingleUsePrivateArraySelects(stmt: Stmt): Stmt = {
    def flattenedArraySize(t: C.AST.Type): Option[BigInt] =
      t match {
        case arr: C.AST.ArrayType =>
          for {
            outer <- arr.size.flatMap(constArith)
            inner <- flattenedArraySize(arr.elemType)
          } yield outer * inner
        case _ =>
          Some(BigInt(1))
      }

    def privateArrayDecl(s: Stmt): Option[(String, BigInt)] =
      s match {
        case DeclStmt(VarDecl(name, arr: C.AST.ArrayType, None)) =>
          flattenedArraySize(arr).map(name -> _)
        case DeclStmt(OpenCL.AST.VarDecl(name, arr: C.AST.ArrayType, addressSpace, None))
            if addressSpace == AddressSpace.Private =>
          flattenedArraySize(arr).map(name -> _)
        case _ =>
          None
      }

    def arrayWrite(name: String, s: Stmt): Option[(Int, Expr)] =
      s match {
        case ExprStmt(Assignment(ArraySubscript(DeclRef(arrayName), idx), rhs))
            if arrayName == name =>
          constInt(idx).map(_ -> rhs)
        case _ =>
          None
      }

    def arrayRead(name: String, expr: Expr): Option[Expr] =
      expr match {
        case ArraySubscript(DeclRef(arrayName), idx) if arrayName == name =>
          Some(idx)
        case _ =>
          None
      }

    def selectAssignment(lhs: Expr, idx: Expr, values: Seq[Expr]): Stmt = {
      def assign(value: Expr): Stmt =
        ExprStmt(Assignment(lhs, value))

      def rec(i: Int): Stmt =
        if (i == values.length - 1) {
          assign(values(i))
        } else {
          IfThenElse(
            BinaryExpr(idx, BinaryOperator.==, Literal(i.toString)),
            assign(values(i)),
            Some(rec(i + 1)))
        }

      rec(0)
    }

    def rewriteBlock(body: Seq[Stmt]): Seq[Stmt] = {
      val out = scala.collection.mutable.ArrayBuffer.empty[Stmt]
      var i = 0
      while (i < body.length) {
        privateArrayDecl(body(i)) match {
          case Some((name, size)) if size > 0 && size <= 16 =>
            val n = size.toInt
            val writes = Array.fill[Option[Expr]](n)(None)
            val kept = scala.collection.mutable.ArrayBuffer.empty[Stmt]
            var j = i + 1
            var consumer: Option[(Expr, Expr)] = None
            var valid = true

            while (j < body.length && consumer.isEmpty && valid) {
              body(j) match {
                case ExprStmt(Assignment(lhs, rhs)) =>
                  arrayRead(name, rhs) match {
                    case Some(idx) =>
                      consumer = Some(lhs -> idx)
                    case None =>
                      arrayWrite(name, body(j)) match {
                        case Some((idx, rhs))
                            if idx >= 0 && idx < n && writes(idx).isEmpty &&
                               !readsAny(body(j), Set(name)) =>
                          writes(idx) = Some(rhs)
                        case Some(_) =>
                          valid = false
                        case None =>
                          if (readsAny(body(j), Set(name)) || writesName(body(j), name)) {
                            valid = false
                          } else {
                            kept += body(j)
                          }
                      }
                  }

                case other =>
                  if (readsAny(other, Set(name)) || writesName(other, name)) {
                    valid = false
                  } else {
                    kept += other
                  }
              }
              j += 1
            }

            val rest = body.drop(j)
            if (
              valid &&
              consumer.isDefined &&
              writes.forall(_.isDefined) &&
              !readsAny(Block(rest), Set(name)) &&
              !writesName(rest, name)
            ) {
              val (lhs, idx) = consumer.get
              out ++= kept
              out += selectAssignment(lhs, idx, writes.flatten.toSeq)
              i = j
            } else {
              out += body(i)
              i += 1
            }
          case _ =>
            out += body(i)
            i += 1
        }
      }
      out.toSeq
    }

    def rec(s: Stmt): Stmt =
      s match {
        case Block(body) =>
          // Code generation often keeps small imperative fragments inside
          // nested Stmts nodes.  The printer later flattens them, but this pass
          // needs the linear statement sequence to see
          //   decl; a[0]=...; ...; out=a[i]
          // as one single-use private-array select pattern.
          Block(rewriteBlock(body.flatMap(stmt => flatten(rec(stmt)))))
        case Stmts(a, b) =>
          blockOrStmt(rewriteBlock(flatten(Stmts(rec(a), rec(b)))))
        case ForLoop(init, cond, increment, body) =>
          ForLoop(
            rec(init).asInstanceOf[DeclStmt],
            cond,
            increment,
            rec(body).asInstanceOf[Block])
        case WhileLoop(cond, body) =>
          WhileLoop(cond, rec(body))
        case IfThenElse(cond, trueBody, falseBody) =>
          IfThenElse(cond, rec(trueBody), falseBody.map(rec))
        case other =>
          other
      }

    rec(stmt)
  }

  def shrinkStaticLocalArrays(
      stmt: Stmt,
      wgConfig: Option[(LocalSize, GlobalSize)]
    ): Stmt = {
    val candidates = collectShrinkCandidates(stmt)
    if (candidates.isEmpty) return stmt

    val maxIndex = scala.collection.mutable.Map.empty[String, BigInt]
    val unsafe = scala.collection.mutable.Set.empty[String]
    val groupIdRanges = workGroupRanges(wgConfig)
    val localIdRangesByDim = localIdRanges(wgConfig)

    def note(name: String, index: Expr, ranges: Map[String, IntRange]): Unit =
      exprRangeWithContext(index, ranges) match {
        case Some(IntRange(lo, hi)) if lo >= 0 =>
          maxIndex.update(name, maxIndex.get(name).fold(hi - 1)(_.max(hi - 1)))
        case _ =>
          unsafe += name
      }

    def expr(e: Expr, ranges: Map[String, IntRange]): Unit =
      e match {
        case ArraySubscript(DeclRef(name), index) if candidates.contains(name) =>
          note(name, index, ranges)
          expr(index, ranges)
        case DeclRef(name) if candidates.contains(name) =>
          unsafe += name
        case ArraySubscript(array, index) =>
          expr(array, ranges); expr(index, ranges)
        case Assignment(lhs, rhs) =>
          expr(lhs, ranges); expr(rhs, ranges)
        case UnaryExpr(_, x) =>
          expr(x, ranges)
        case BinaryExpr(l, _, r) =>
          expr(l, ranges); expr(r, ranges)
        case TernaryExpr(c, t, f) =>
          expr(c, ranges); expr(t, ranges); expr(f, ranges)
        case FunCall(fn, args) =>
          expr(fn, ranges); args.foreach(expr(_, ranges))
        case Cast(_, x) =>
          expr(x, ranges)
        case StructMemberAccess(x, _) =>
          expr(x, ranges)
        case _ =>
      }

    def collect(
        s: Stmt,
        ranges: Map[String, IntRange],
        localRanges: Map[Int, IntRange]
      ): Unit =
      s match {
        case Block(body) =>
          var r = ranges
          body.foreach {
            case d @ DeclStmt(VarDecl(name, BasicType("int", _), Some(init))) =>
              expr(init, r)
              builtInIdRange(init, groupIdRanges, localRanges)
                .orElse(exprRangeWithContext(init, r))
                .orElse(arithmeticExprRange(init))
                .orElse(constInt(init).map(n => IntRange(n, BigInt(n) + 1)))
                .foreach(range => r += name -> range)
            case other =>
              collect(other, r, localRanges)
          }
        case Stmts(a, b) =>
          collect(a, ranges, localRanges); collect(b, ranges, localRanges)
        case ForLoop(init, cond, increment, body) =>
          collect(init, ranges, localRanges); expr(cond, ranges); expr(increment, ranges)
          val loopRanges = loopRange(init.asInstanceOf[DeclStmt], cond)
            .orElse(localIdStartedLoopRange(init.asInstanceOf[DeclStmt], cond, localRanges))
            .map { case (name, range) => ranges + (name -> range) }
            .getOrElse(ranges)
          collect(body, loopRanges, localRanges)
        case WhileLoop(cond, body) =>
          expr(cond, ranges); collect(body, ranges, localRanges)
        case IfThenElse(cond, trueBody, falseBody) =>
          expr(cond, ranges)
          collect(
            trueBody,
            refineTrueBranchRanges(cond, ranges),
            refineTrueLocalIdRanges(cond, localRanges))
          falseBody.foreach(collect(_, ranges, localRanges))
        case DeclStmt(VarDecl(_, _, init)) =>
          init.foreach(expr(_, ranges))
        case ExprStmt(x) =>
          expr(x, ranges)
        case _ =>
      }

    collect(stmt, Map.empty, localIdRangesByDim)
    val replacements = candidates.flatMap { case (name, (oldSize, _)) =>
      maxIndex.get(name)
        .map(_ + 1)
        .filter(newSize => newSize > 0 && newSize < oldSize && !unsafe(name))
        .map(name -> _)
    }
    if (replacements.isEmpty) stmt else rewriteArraySizes(stmt, replacements)
  }

  private def refineTrueBranchRanges(
      cond: Expr,
      ranges: Map[String, IntRange]
    ): Map[String, IntRange] =
    cond match {
      case BinaryExpr(DeclRef(name), BinaryOperator.<, bound) =>
        exprRangeWithContext(bound, ranges)
          .orElse(constInt(bound).map(n => IntRange(n, BigInt(n) + 1)))
          .flatMap(_.singleton)
          .flatMap(hi => ranges.get(name).map(r => name -> IntRange(r.lo, r.hiExclusive.min(hi))))
          .map { case (n, r) => ranges + (n -> r) }
          .getOrElse(ranges)
      case _ =>
        ranges
    }

  private def refineTrueLocalIdRanges(
      cond: Expr,
      ranges: Map[Int, IntRange]
    ): Map[Int, IntRange] =
    cond match {
      case BinaryExpr(localIdCall(dim), BinaryOperator.<, bound) =>
        constInt(bound)
          .flatMap(hi => ranges.get(dim).map(r => dim -> IntRange(r.lo, r.hiExclusive.min(BigInt(hi)))))
          .map { case (dim, range) => ranges + (dim -> range) }
          .getOrElse(ranges)
      case _ =>
        ranges
    }

  private def collectShrinkCandidates(stmt: Stmt): Map[String, (BigInt, C.AST.ArrayType)] = {
    val out = scala.collection.mutable.Map.empty[String, (BigInt, C.AST.ArrayType)]
    def loop(s: Stmt): Unit =
      s match {
        case Block(body) => body.foreach(loop)
        case Stmts(a, b) => loop(a); loop(b)
        case ForLoop(init, _, _, body) => loop(init); loop(body)
        case WhileLoop(_, body) => loop(body)
        case IfThenElse(_, t, f) => loop(t); f.foreach(loop)
        case DeclStmt(OpenCL.AST.VarDecl(name, arr: C.AST.ArrayType, addressSpace, None))
            if addressSpace == AddressSpace.Local || addressSpace == AddressSpace.Private =>
          arr.size.flatMap(constArith).foreach(size => out += name -> (size, arr))
        case DeclStmt(VarDecl(name, arr: C.AST.ArrayType, None)) =>
          arr.size.flatMap(constArith).foreach(size => out += name -> (size, arr))
        case _ =>
      }
    loop(stmt)
    out.toMap
  }

  private def rewriteArraySizes(stmt: Stmt, replacements: Map[String, BigInt]): Stmt =
    stmt match {
      case Block(body) =>
        Block(body.map(rewriteArraySizes(_, replacements)))
      case Stmts(a, b) =>
        Stmts(rewriteArraySizes(a, replacements), rewriteArraySizes(b, replacements))
      case ForLoop(init, cond, increment, body) =>
        ForLoop(
          rewriteArraySizes(init, replacements).asInstanceOf[DeclStmt],
          cond,
          increment,
          rewriteArraySizes(body, replacements).asInstanceOf[Block])
      case WhileLoop(cond, body) =>
        WhileLoop(cond, rewriteArraySizes(body, replacements))
      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, rewriteArraySizes(trueBody, replacements), falseBody.map(rewriteArraySizes(_, replacements)))
      case DeclStmt(v: OpenCL.AST.VarDecl) if replacements.contains(v.name) =>
        DeclStmt(withArraySize(v, replacements(v.name)))
      case DeclStmt(v: VarDecl) if replacements.contains(v.name) =>
        DeclStmt(withArraySize(v, replacements(v.name)))
      case other =>
        other
    }

  private def withArraySize(decl: VarDecl, size: BigInt): VarDecl = {
    val arr = decl.t.asInstanceOf[C.AST.ArrayType]
    val t = C.AST.ArrayType(arr.elemType, Some(Cst(size.toLong)), arr.const)
    decl match {
      case v: OpenCL.AST.VarDecl =>
        OpenCL.AST.VarDecl(v.name, t, v.addressSpace, v.init)
      case v =>
        VarDecl(v.name, t, v.init)
    }
  }

  private def dropTrailingWorkGroupBarriers(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        Block(body.map(dropTrailingWorkGroupBarriers))
      case Stmts(a, b) =>
        Stmts(dropTrailingWorkGroupBarriers(a), dropTrailingWorkGroupBarriers(b))
      case ForLoop(init, cond, increment, body) =>
        val rewrittenBody = dropTrailingWorkGroupBarriers(body).asInstanceOf[Block]
        val finalBody =
          if (isWorkGroupStridedLoop(init.asInstanceOf[DeclStmt], increment))
            dropTrailingLocalBarriers(rewrittenBody)
          else
            rewrittenBody
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment, finalBody)
      case WhileLoop(cond, body) =>
        WhileLoop(cond, dropTrailingWorkGroupBarriers(body))
      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, dropTrailingWorkGroupBarriers(trueBody), falseBody.map(dropTrailingWorkGroupBarriers))
      case other =>
        other
    }

  private def dropTrailingLocalBarriers(block: Block): Block = {
    val trimmed = block.body.reverse.dropWhile(isLocalBarrierOnly).reverse
    Block(trimmed)
  }

  private def isWorkGroupStridedLoop(init: DeclStmt, increment: Expr): Boolean =
    init match {
      case DeclStmt(VarDecl(name, _, Some(start))) =>
        exprContainsOpenCLQuery(start, "get_group_id") &&
          referencesName(increment, name) &&
          exprContainsOpenCLQuery(increment, "get_num_groups")
      case _ =>
        false
    }

  private def exprContainsOpenCLQuery(expr: Expr, query: String): Boolean = {
    var found = false
    Nodes.VisitAndRebuild(expr, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result =
        n match {
          case FunCall(DeclRef(`query`), _) =>
            found = true
            Stop(n)
          case ArithmeticExpr(ae) if ae.toString.contains(s"$query(") =>
            found = true
            Stop(n)
          case Literal(text) if text.contains(s"$query(") =>
            found = true
            Stop(n)
          case _ =>
            Continue(n, this)
        }
    })
    found
  }

  private def referencesName(expr: Expr, name: String): Boolean = {
    var found = false
    Nodes.VisitAndRebuild(expr, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result =
        n match {
          case DeclRef(`name`) =>
            found = true
            Stop(n)
          case ArithmeticExpr(ae) if ae.toString.contains(name) =>
            found = true
            Stop(n)
          case Literal(text) if text.contains(name) =>
            found = true
            Stop(n)
          case _ =>
            Continue(n, this)
        }
    })
    found
  }

  private def repairLocalDependencyBarriers(stmt: Stmt, localNames: Set[String]): Stmt =
    stmt match {
      case Block(body) =>
        Block(repairLocalDependencyBarrierBlock(body, localNames))
      case Stmts(a, b) =>
        blockOrStmt(repairLocalDependencyBarrierBlock(flatten(Stmts(a, b)), localNames))
      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
          repairLocalDependencyBarriers(body, localNames).asInstanceOf[Block])
      case WhileLoop(cond, body) =>
        WhileLoop(cond, repairLocalDependencyBarriers(body, localNames))
      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, repairLocalDependencyBarriers(trueBody, localNames),
          falseBody.map(repairLocalDependencyBarriers(_, localNames)))
      case other =>
        other
    }

  private def repairLocalDependencyBarrierBlock(
      stmts: Seq[Stmt],
      localNames: Set[String]
    ): Seq[Stmt] = {
    val out = scala.collection.mutable.ArrayBuffer.empty[Stmt]
    var sinceBarrier = LocalEffects()
    stmts.foreach { raw =>
      val stmt = repairLocalDependencyBarriers(raw, localNames)
      if (isLocalBarrierOnly(stmt)) {
        out += stmt
        sinceBarrier = LocalEffects()
      } else {
        val effects = localEffects(stmt, localNames)
        if (needsLocalBarrier(sinceBarrier, effects) && !out.lastOption.exists(isLocalBarrierOnly)) {
          out += shine.OpenCL.AST.Barrier(local = true, global = false)
          sinceBarrier = LocalEffects()
        }
        out += stmt
        sinceBarrier = sinceBarrier ++ effects
      }
    }
    out.toSeq
  }

  private def needsLocalBarrier(a: LocalEffects, b: LocalEffects): Boolean =
    a.writes.intersect(b.reads).nonEmpty || a.reads.intersect(b.writes).nonEmpty

  private case class IntRange(lo: BigInt, hiExclusive: BigInt) {
    def +(other: IntRange): IntRange =
      IntRange(lo + other.lo, hiExclusive + other.hiExclusive - 1)

    def *(coef: BigInt): IntRange =
      if (coef >= 0) {
        IntRange(lo * coef, (hiExclusive - 1) * coef + 1)
      } else {
        IntRange((hiExclusive - 1) * coef, lo * coef + 1)
      }

    def nonNegativeAndBelow(n: BigInt): Boolean =
      lo >= 0 && hiExclusive <= n

    def singleton: Option[BigInt] =
      if (hiExclusive == lo + 1) Some(lo) else None
  }

  private case class LinearInt(const: BigInt, terms: Map[String, BigInt]) {
    def +(other: LinearInt): LinearInt =
      LinearInt(const + other.const, mergeTerms(terms, other.terms, _ + _))

    def -(other: LinearInt): LinearInt =
      LinearInt(const - other.const, mergeTerms(terms, other.terms, _ - _))

    def *(coef: BigInt): LinearInt =
      LinearInt(const * coef, terms.map { case (name, c) => name -> (c * coef) })

    def /(divisor: BigInt): LinearInt =
      LinearInt(const / divisor, terms.map { case (name, c) => name -> (c / divisor) })

    def splitDivisibleBy(divisor: BigInt): (LinearInt, LinearInt) = {
      val divisibleTerms = terms.collect { case (name, coef) if coef % divisor == 0 => name -> coef }
      val remainderTerms = terms.collect { case (name, coef) if coef % divisor != 0 => name -> coef }
      val divConst = if (const % divisor == 0) const else BigInt(0)
      val remConst = const - divConst
      LinearInt(divConst, divisibleTerms) -> LinearInt(remConst, remainderTerms)
    }

    def isZero: Boolean =
      const == 0 && terms.values.forall(_ == 0)
  }

  private def mergeTerms(
      lhs: Map[String, BigInt],
      rhs: Map[String, BigInt],
      merge: (BigInt, BigInt) => BigInt
    ): Map[String, BigInt] =
    (lhs.keySet ++ rhs.keySet).flatMap { name =>
      val v = merge(lhs.getOrElse(name, BigInt(0)), rhs.getOrElse(name, BigInt(0)))
      if (v == 0) None else Some(name -> v)
    }.toMap

  private def workGroupRanges(
      wgConfig: Option[(LocalSize, GlobalSize)]
    ): Map[Int, IntRange] =
    wgConfig match {
      case Some((LocalSize(local), GlobalSize(global))) =>
        (0 to 2).flatMap { dim =>
          for {
            l <- constNat(local(dim))
            g <- constNat(global(dim))
            if l != 0 && g % l == 0
          } yield dim -> IntRange(0, g / l)
        }.toMap
      case None =>
        Map.empty
    }

  private def localIdRanges(
      wgConfig: Option[(LocalSize, GlobalSize)]
    ): Map[Int, IntRange] =
    wgConfig match {
      case Some((LocalSize(local), _)) =>
        (0 to 2).flatMap { dim =>
          constNat(local(dim)).map { l =>
            dim -> IntRange(0, l)
          }
        }.toMap
      case None =>
        Map.empty
    }

  private def constNat(n: shine.DPIA.Nat): Option[BigInt] =
    n match {
      case Cst(value) => Some(value)
      case _ => None
    }

  private def simplifyIntegerExpressionsWithRanges(
      stmt: Stmt,
      groupRanges: Map[Int, IntRange],
      localRanges: Map[Int, IntRange]
    ): Stmt = {
    val (rewritten, _) = simplifyStmtWithIntegerContext(
      stmt,
      groupRanges,
      localRanges,
      ranges = Map.empty,
      intDecls = Map.empty
    )
    rewritten
  }

  private def simplifyStmtWithIntegerContext(
      stmt: Stmt,
      groupRanges: Map[Int, IntRange],
      localRanges: Map[Int, IntRange],
      ranges: Map[String, IntRange],
      intDecls: Map[String, Expr]
    ): (Stmt, Map[String, Expr]) =
    stmt match {
      case Block(body) =>
        val rewritten = scala.collection.mutable.ArrayBuffer.empty[Stmt]
        var currentRanges = ranges
        var currentDecls = intDecls
        body.foreach { s =>
          val (newStmt, newDecls, newRanges) =
            simplifyBlockStmt(s, groupRanges, localRanges, currentRanges, currentDecls)
          rewritten += newStmt
          currentDecls = newDecls
          currentRanges = newRanges
        }
        Block(rewritten.toSeq) -> intDecls

      case Stmts(a, b) =>
        val (ra, envA) = simplifyStmtWithIntegerContext(a, groupRanges, localRanges, ranges, intDecls)
        val (rb, envB) = simplifyStmtWithIntegerContext(b, groupRanges, localRanges, ranges, envA)
        Stmts(ra, rb) -> envB

      case ForLoop(init, cond, increment, body) =>
        val initDecl = init.asInstanceOf[DeclStmt]
        val loopRanges = loopRange(initDecl, cond)
          .orElse(localIdStartedLoopRange(initDecl, cond, localRanges))
          .map { case (name, range) => ranges + (name -> range) }
          .getOrElse(ranges)
        val (rewrittenBody, _) =
          simplifyStmtWithIntegerContext(body, groupRanges, localRanges, loopRanges, intDecls)
        ForLoop(initDecl, cond, increment,
          rewrittenBody.asInstanceOf[Block]) -> intDecls

      case WhileLoop(cond, body) =>
        val (rewrittenBody, _) =
          simplifyStmtWithIntegerContext(body, groupRanges, localRanges, ranges, intDecls)
        WhileLoop(cond, rewrittenBody) -> intDecls

      case IfThenElse(cond, trueBody, falseBody) =>
        val rewrittenCond = simplifyIntegerExprWithContext(cond, ranges, intDecls)
        val (rewrittenTrue, _) =
          simplifyStmtWithIntegerContext(
            trueBody,
            groupRanges,
            refineTrueLocalIdRanges(rewrittenCond, localRanges),
            refineTrueBranchRanges(rewrittenCond, ranges),
            intDecls)
        val rewrittenFalse = falseBody.map { fb =>
          simplifyStmtWithIntegerContext(fb, groupRanges, localRanges, ranges, intDecls)._1
        }
        IfThenElse(
          rewrittenCond,
          rewrittenTrue,
          rewrittenFalse
        ) -> intDecls

      case ExprStmt(Assignment(lhs, rhs)) =>
        ExprStmt(Assignment(
          simplifyIntegerExprWithContext(lhs, ranges, intDecls),
          simplifyIntegerExprWithContext(rhs, ranges, intDecls)
        )) -> intDecls

      case other =>
        other -> intDecls
    }

  private def simplifyBlockStmt(
      stmt: Stmt,
      groupRanges: Map[Int, IntRange],
      localRanges: Map[Int, IntRange],
      ranges: Map[String, IntRange],
      intDecls: Map[String, Expr]
    ): (Stmt, Map[String, Expr], Map[String, IntRange]) =
    stmt match {
      case DeclStmt(VarDecl(name, t @ BasicType("int", _), Some(init))) =>
        val rewrittenInit = simplifyIntegerExprWithContext(init, ranges, intDecls)
        val initRange = builtInIdRange(rewrittenInit, groupRanges, localRanges)
          .orElse(arithmeticExprRange(rewrittenInit))
          .orElse(exprRangeWithContext(rewrittenInit, ranges))
        val normalizedInit = initRange.flatMap(_.singleton)
          .map(v => Literal(v.toString))
          .getOrElse(rewrittenInit)
        val nextRanges = initRange
          .map(r => ranges + (name -> r))
          .getOrElse(ranges)
        val nextDecls =
          if (integerPure(normalizedInit) && cPrinterKey(normalizedInit).isDefined)
            intDecls + (name -> normalizedInit)
          else intDecls - name
        (DeclStmt(VarDecl(name, t, Some(normalizedInit))), nextDecls, nextRanges)

      case other =>
        val (rewritten, nextDecls) =
          simplifyStmtWithIntegerContext(other, groupRanges, localRanges, ranges, intDecls)
        (rewritten, nextDecls, ranges)
    }

  private def builtInIdRange(
      expr: Expr,
      groupRanges: Map[Int, IntRange],
      localRanges: Map[Int, IntRange]
    ): Option[IntRange] =
    expr match {
      case FunCall(DeclRef("get_group_id"), Seq(Literal(dimText))) =>
        dimText.toIntOption.flatMap(groupRanges.get)
      case FunCall(DeclRef("get_group_id"), Seq(ArithmeticExpr(Cst(dim)))) =>
        groupRanges.get(dim.toInt)
      case FunCall(DeclRef("get_local_id"), Seq(Literal(dimText))) =>
        dimText.toIntOption.flatMap(localRanges.get)
      case FunCall(DeclRef("get_local_id"), Seq(ArithmeticExpr(Cst(dim)))) =>
        localRanges.get(dim.toInt)
      case ArithmeticExpr(b: BuiltInFunctionCall)
          if b.toString == s"get_group_id(${b.param})" =>
        groupRanges.get(b.param)
      case ArithmeticExpr(b: BuiltInFunctionCall)
          if b.toString == s"get_local_id(${b.param})" =>
        localRanges.get(b.param)
      case ArithmeticExpr(ae) if ae.toString.startsWith("get_group_id(") =>
        val dim = ae.toString.stripPrefix("get_group_id(").stripSuffix(")")
        dim.toIntOption.flatMap(groupRanges.get)
      case ArithmeticExpr(ae) if ae.toString.startsWith("get_local_id(") =>
        val dim = ae.toString.stripPrefix("get_local_id(").stripSuffix(")")
        dim.toIntOption.flatMap(localRanges.get)
      case Literal(text) if text.startsWith("get_group_id(") =>
        val dim = text.stripPrefix("get_group_id(").stripSuffix(")")
        dim.toIntOption.flatMap(groupRanges.get)
      case Literal(text) if text.startsWith("get_local_id(") =>
        val dim = text.stripPrefix("get_local_id(").stripSuffix(")")
        dim.toIntOption.flatMap(localRanges.get)
      case _ =>
        None
    }

  private def arithmeticExprRange(expr: Expr): Option[IntRange] =
    expr match {
      case ArithmeticExpr(ae) =>
        for {
          lo <- constArith(ae.min)
          hi <- constArith(ae.max)
        } yield IntRange(lo, hi + 1)
      case _ =>
        None
    }

  private def constArith(ae: arithexpr.arithmetic.ArithExpr): Option[BigInt] =
    ae match {
      case Cst(value) => Some(value)
      case _ => None
    }

  private def loopRange(init: DeclStmt, cond: Expr): Option[(String, IntRange)] =
    (init, cond) match {
      case (
          DeclStmt(VarDecl(name, BasicType("int", _), Some(start))),
          BinaryExpr(DeclRef(condName), BinaryOperator.<, end)
        ) if name == condName =>
        for {
          lo <- constInt(start)
          hi <- constInt(end)
        } yield name -> IntRange(lo, hi)
      case _ =>
        None
    }

  private def localIdStartedLoopRange(
      init: DeclStmt,
      cond: Expr,
      localRanges: Map[Int, IntRange]
    ): Option[(String, IntRange)] =
    (init, cond) match {
      case (
          DeclStmt(VarDecl(name, BasicType("int", _), Some(start))),
          BinaryExpr(DeclRef(condName), BinaryOperator.<, end)
        ) if name == condName =>
        for {
          startRange <- builtInIdRange(start, Map.empty, localRanges)
          hi <- constInt(end)
          if startRange.lo >= 0 && BigInt(hi) >= startRange.lo
        } yield name -> IntRange(startRange.lo, hi)
      case _ =>
        None
    }

  private def simplifyIntegerExprWithContext(
      expr: Expr,
      ranges: Map[String, IntRange],
      intDecls: Map[String, Expr]
    ): Expr = {
    val childrenSimplified = expr match {
      case BinaryExpr(lhs, op, rhs) =>
        BinaryExpr(
          simplifyIntegerExprWithContext(lhs, ranges, intDecls),
          op,
          simplifyIntegerExprWithContext(rhs, ranges, intDecls)
        )
      case UnaryExpr(op, e) =>
        UnaryExpr(op, simplifyIntegerExprWithContext(e, ranges, intDecls))
      case TernaryExpr(cond, thenE, elseE) =>
        TernaryExpr(
          simplifyIntegerExprWithContext(cond, ranges, intDecls),
          simplifyIntegerExprWithContext(thenE, ranges, intDecls),
          simplifyIntegerExprWithContext(elseE, ranges, intDecls)
        )
      case ArraySubscript(array, index) =>
        ArraySubscript(array, simplifyIntegerExprWithContext(index, ranges, intDecls))
      case Cast(t, e) =>
        Cast(t, simplifyIntegerExprWithContext(e, ranges, intDecls))
      case other =>
        other
    }

    val simplified = childrenSimplified match {
      case DeclRef(name) =>
        ranges.get(name).flatMap(_.singleton)
          .map(v => Literal(v.toString))
          .getOrElse(simplifyExpr(childrenSimplified))
      case BinaryExpr(BinaryExpr(dividend, BinaryOperator./, div), BinaryOperator.%, mod) =>
        simplifyLinearDivModulo(dividend, div, mod, ranges, intDecls)
          .getOrElse(simplifyLinearModulo(
            BinaryExpr(dividend, BinaryOperator./, div),
            mod,
            ranges,
            intDecls
          ))
      case BinaryExpr(lhs, BinaryOperator.%, rhs) =>
        val linear = simplifyLinearModulo(lhs, rhs, ranges, intDecls)
        if (sameExpr(linear, BinaryExpr(lhs, BinaryOperator.%, rhs)))
          simplifyPowerOfTwoModulo(lhs, rhs, ranges, intDecls).getOrElse(linear)
        else linear
      case BinaryExpr(lhs, BinaryOperator./, rhs) =>
        val linear = simplifyLinearDivision(lhs, rhs, ranges, intDecls)
        if (sameExpr(linear, BinaryExpr(lhs, BinaryOperator./, rhs)))
          simplifyPowerOfTwoDivision(lhs, rhs, ranges, intDecls).getOrElse(linear)
        else linear
      case BinaryExpr(lhs, BinaryOperator.>>, rhs) =>
        simplifyShiftRight(lhs, rhs, ranges, intDecls)
      case BinaryExpr(lhs, BinaryOperator.bitAnd, rhs) =>
        simplifyBitAnd(lhs, rhs, ranges, intDecls)
      case BinaryExpr(lhs, op, rhs) =>
        simplifyRangeComparison(lhs, op, rhs, ranges, intDecls)
          .getOrElse(simplifyBinary(lhs, op, rhs))
      case other =>
        simplifyExpr(other)
    }
    reuseKnownIntegerDecl(simplified, intDecls).getOrElse(simplified)
  }

  private def reuseKnownIntegerDecl(
      expr: Expr,
      intDecls: Map[String, Expr]
    ): Option[Expr] =
    if (reusableKnownIntegerExpr(expr)) {
      cPrinterKey(expr).flatMap { key =>
        intDecls.toSeq.sortBy(_._1).collectFirst {
          case (name, known) if cPrinterKey(known).contains(key) => DeclRef(name)
        }
      }.orElse(reuseKnownIntegerDeclStructuralOffset(expr, intDecls))
       .orElse(reuseKnownIntegerDeclWithOffset(expr, intDecls))
    } else {
      None
    }

  private def cPrinterKey(expr: Expr): Option[String] =
    try Some(C.AST.Printer(expr))
    catch { case _: Exception => None }

  private def reuseKnownIntegerDeclStructuralOffset(
      expr: Expr,
      intDecls: Map[String, Expr]
    ): Option[Expr] =
    expr match {
      case BinaryExpr(base, BinaryOperator.+, Literal(offset))
          if offset.toIntOption.exists(_ != 0) =>
        reuseKnownIntegerDecl(base, intDecls).collect {
          case DeclRef(name)
              if exprSize(BinaryExpr(DeclRef(name), BinaryOperator.+, Literal(offset))) < exprSize(expr) =>
            BinaryExpr(DeclRef(name), BinaryOperator.+, Literal(offset))
        }
      case BinaryExpr(base, BinaryOperator.-, Literal(offset))
          if offset.toIntOption.exists(_ != 0) =>
        reuseKnownIntegerDecl(base, intDecls).collect {
          case DeclRef(name)
              if exprSize(BinaryExpr(DeclRef(name), BinaryOperator.-, Literal(offset))) < exprSize(expr) =>
            BinaryExpr(DeclRef(name), BinaryOperator.-, Literal(offset))
        }
      case _ =>
        None
    }

  private def reuseKnownIntegerDeclWithOffset(
      expr: Expr,
      intDecls: Map[String, Expr]
    ): Option[Expr] =
    linearOf(expr, intDecls).flatMap { exprLinear =>
      intDecls.toSeq.sortBy(_._1).collectFirst {
        case (name, known)
            if linearOf(known, intDecls).exists { knownLinear =>
              val delta = exprLinear - knownLinear
              delta.terms.isEmpty && delta.const != 0 && {
                val replacement =
                  if (delta.const > 0)
                    BinaryExpr(DeclRef(name), BinaryOperator.+, Literal(delta.const.toString))
                  else
                    BinaryExpr(DeclRef(name), BinaryOperator.-, Literal((-delta.const).toString))
                exprSize(replacement) < exprSize(expr)
              }
            } =>
          val delta = exprLinear - linearOf(known, intDecls).get
          if (delta.const > 0)
            BinaryExpr(DeclRef(name), BinaryOperator.+, Literal(delta.const.toString))
          else
            BinaryExpr(DeclRef(name), BinaryOperator.-, Literal((-delta.const).toString))
      }
    }

  private def reusableKnownIntegerExpr(expr: Expr): Boolean =
    integerPure(expr) && !atomic(expr) &&
      (containsIntegerDivOrMod(expr) || containsShiftOrMask(expr))

  private def simplifyRangeComparison(
      lhs: Expr,
      op: BinaryOperator.Value,
      rhs: Expr,
      ranges: Map[String, IntRange],
      intDecls: Map[String, Expr]
    ): Option[Expr] =
    for {
      l <- rangeOfExpr(lhs, ranges, intDecls)
      r <- rangeOfExpr(rhs, ranges, intDecls)
      value <- compareRanges(l, op, r)
    } yield Literal(if (value) "1" else "0")

  private def compareRanges(
      lhs: IntRange,
      op: BinaryOperator.Value,
      rhs: IntRange
    ): Option[Boolean] = {
    val lhsMax = lhs.hiExclusive - 1
    val rhsMax = rhs.hiExclusive - 1
    op match {
      case BinaryOperator.< if lhsMax < rhs.lo => Some(true)
      case BinaryOperator.< if lhs.lo >= rhsMax => Some(false)
      case BinaryOperator.<= if lhsMax <= rhs.lo => Some(true)
      case BinaryOperator.<= if lhs.lo > rhsMax => Some(false)
      case BinaryOperator.> if lhs.lo > rhsMax => Some(true)
      case BinaryOperator.> if lhsMax <= rhs.lo => Some(false)
      case BinaryOperator.>= if lhs.lo >= rhsMax => Some(true)
      case BinaryOperator.>= if lhsMax < rhs.lo => Some(false)
      case BinaryOperator.== if lhs.lo == lhsMax && rhs.lo == rhsMax && lhs.lo == rhs.lo => Some(true)
      case BinaryOperator.== if lhsMax < rhs.lo || rhsMax < lhs.lo => Some(false)
      case BinaryOperator.!= if lhs.lo == lhsMax && rhs.lo == rhsMax && lhs.lo == rhs.lo => Some(false)
      case BinaryOperator.!= if lhsMax < rhs.lo || rhsMax < lhs.lo => Some(true)
      case _ => None
    }
  }

  private def rangeOfExpr(
      expr: Expr,
      ranges: Map[String, IntRange],
      intDecls: Map[String, Expr],
      seen: Set[String] = Set.empty
    ): Option[IntRange] =
    expr match {
      case Literal(text) =>
        text.toIntOption.map(v => IntRange(v, v + 1))
      case ArithmeticExpr(Cst(value)) =>
        Some(IntRange(value, value + 1))
      case ArithmeticExpr(_) =>
        arithmeticExprRange(expr)
      case DeclRef(name) =>
        ranges.get(name)
          .orElse {
            if (seen.contains(name)) None
            else intDecls.get(name).flatMap(rangeOfExpr(_, ranges, intDecls, seen + name))
          }
      case BinaryExpr(lhs, BinaryOperator.+, rhs) =>
        for { l <- rangeOfExpr(lhs, ranges, intDecls, seen); r <- rangeOfExpr(rhs, ranges, intDecls, seen) } yield l + r
      case BinaryExpr(lhs, BinaryOperator.-, rhs) =>
        for { l <- rangeOfExpr(lhs, ranges, intDecls, seen); r <- rangeOfExpr(rhs, ranges, intDecls, seen) } yield l + (r * BigInt(-1))
      case BinaryExpr(lhs, BinaryOperator.*, rhs) =>
        (constInt(lhs), constInt(rhs)) match {
          case (Some(c), _) => rangeOfExpr(rhs, ranges, intDecls, seen).map(_ * BigInt(c))
          case (_, Some(c)) => rangeOfExpr(lhs, ranges, intDecls, seen).map(_ * BigInt(c))
          case _ => None
        }
      case BinaryExpr(lhs, BinaryOperator./, rhs) =>
        constInt(rhs)
          .filter(_ > 0)
          .flatMap { d =>
            rangeOfExpr(lhs, ranges, intDecls, seen).collect {
              case r if r.lo >= 0 => IntRange(r.lo / d, ((r.hiExclusive - 1) / d) + 1)
            }
          }
      case BinaryExpr(lhs, BinaryOperator.>>, rhs) =>
        constInt(rhs)
          .filter(_ >= 0)
          .flatMap { shift =>
            rangeOfExpr(lhs, ranges, intDecls, seen).collect {
              case r if r.lo >= 0 => IntRange(r.lo >> shift, ((r.hiExclusive - 1) >> shift) + 1)
            }
          }
      case BinaryExpr(_, BinaryOperator.%, rhs) =>
        constInt(rhs)
          .filter(_ > 0)
          .map(d => IntRange(0, d))
      case BinaryExpr(_, BinaryOperator.bitAnd, rhs) =>
        constInt(rhs)
          .filter(_ >= 0)
          .map(mask => IntRange(0, BigInt(mask) + 1))
      case Cast(BasicType("int", _), e) =>
        rangeOfExpr(e, ranges, intDecls, seen)
      case _ =>
        None
    }

  private def simplifyLinearModulo(
      lhs: Expr,
      rhs: Expr,
      ranges: Map[String, IntRange],
      intDecls: Map[String, Expr]
    ): Expr =
    constInt(rhs)
      .filter(_ != 0)
      .flatMap { divisor =>
        linearOf(lhs, intDecls).flatMap { linear =>
          val (_, remainder) = linear.splitDivisibleBy(divisor)
          rangeOf(remainder, ranges).collect {
            case r if r.nonNegativeAndBelow(divisor) =>
              linearToExpr(remainder)
            case r if r.lo >= 0 && remainder.terms.isEmpty =>
              linearToExpr(remainder.copy(const = positiveMod(remainder.const, divisor)))
          }.orElse {
            val (divisible, rem) = linear.splitDivisibleBy(divisor)
            if (!divisible.isZero && rem.isZero) Some(Literal("0"))
            else if (!divisible.isZero) Some(simplifyModulo(linearToExpr(rem), rhs))
            else None
          }
        }
      }
      .getOrElse(simplifyModulo(lhs, rhs))

  private def simplifyLinearDivModulo(
      dividend: Expr,
      divExpr: Expr,
      modExpr: Expr,
      ranges: Map[String, IntRange],
      intDecls: Map[String, Expr]
    ): Option[Expr] =
    for {
      divisor <- constInt(divExpr).filter(_ > 0)
      modulus <- constInt(modExpr).filter(_ > 0)
      linear <- linearOf(dividend, intDecls)
      simplified <- {
        val (divisible, remainder) = linear.splitDivisibleBy(divisor)
        val splitQuotient =
          if (!divisible.isZero && !remainder.isZero)
            rangeOf(remainder, ranges)
              .filter(_.lo >= 0)
              .map { _ =>
                BinaryExpr(
                  BinaryExpr(
                    linearToExpr(divisible / divisor),
                    BinaryOperator.+,
                    BinaryExpr(linearToExpr(remainder), BinaryOperator./,
                      Literal(divisor.toString))
                  ),
                  BinaryOperator.%,
                  Literal(modulus.toString)
                )
              }
          else None
        splitQuotient.orElse {
          val (_, rem) = linear.splitDivisibleBy(divisor * modulus)
          for {
            remRange <- rangeOf(rem, ranges)
            if remRange.nonNegativeAndBelow(divisor * modulus)
          } yield BinaryExpr(
            linearToExpr(rem),
            BinaryOperator./,
            Literal(divisor.toString)
          )
        }
      }
    } yield simplifyIntegerExprWithContext(simplified, ranges, intDecls)

  private def simplifyLinearDivision(
      lhs: Expr,
      rhs: Expr,
      ranges: Map[String, IntRange],
      intDecls: Map[String, Expr]
    ): Expr =
    constInt(rhs)
      .filter(_ != 0)
      .flatMap { divisor =>
        linearOf(lhs, intDecls).flatMap { linear =>
          val (divisible, remainder) = linear.splitDivisibleBy(divisor)
          for {
            fullRange <- rangeOf(linear, ranges)
            remRange <- rangeOf(remainder, ranges)
            if fullRange.lo >= 0 &&
              (remRange.nonNegativeAndBelow(divisor) || (remRange.lo >= 0 && remainder.terms.isEmpty))
          } yield {
            val quotientRemainder =
              if (remRange.nonNegativeAndBelow(divisor)) {
                LinearInt(0, Map.empty)
              } else {
                floorDivLinearConst(remainder, divisor)
              }
            linearToExpr((divisible / divisor) + quotientRemainder)
          }
        }
      }
      .orElse(simplifyFactoredDivision(lhs, rhs, ranges, intDecls))
      .getOrElse(simplifyBinary(lhs, BinaryOperator./, rhs))

  private def simplifyFactoredDivision(
      lhs: Expr,
      rhs: Expr,
      ranges: Map[String, IntRange],
      intDecls: Map[String, Expr]
    ): Option[Expr] =
    for {
      divisor <- constInt(rhs).filter(_ > 1)
      linear <- linearOf(lhs, intDecls)
      factor <- properDivisorsDescending(divisor).find { f =>
        val (_, remainder) = linear.splitDivisibleBy(f)
        rangeOf(remainder, ranges).exists(_.nonNegativeAndBelow(f))
      }
      (divisible, _) = linear.splitDivisibleBy(factor)
      if !divisible.isZero
    } yield simplifyIntegerExprWithContext(
      BinaryExpr(linearToExpr(divisible / factor), BinaryOperator./,
        Literal((divisor / factor).toString)),
      ranges,
      intDecls
      )

  private def simplifyPowerOfTwoDivision(
      lhs: Expr,
      rhs: Expr,
      ranges: Map[String, IntRange],
      intDecls: Map[String, Expr]
    ): Option[Expr] =
    for {
      shift <- powerOfTwoShift(rhs)
      lhsRange <- rangeOfExpr(lhs, ranges, intDecls)
      if lhsRange.lo >= 0
    } yield simplifyShiftRight(lhs, Literal(shift.toString), ranges, intDecls)

  private def simplifyPowerOfTwoModulo(
      lhs: Expr,
      rhs: Expr,
      ranges: Map[String, IntRange],
      intDecls: Map[String, Expr]
    ): Option[Expr] =
    for {
      shift <- powerOfTwoShift(rhs)
      lhsRange <- rangeOfExpr(lhs, ranges, intDecls)
      if lhsRange.lo >= 0
      mask = (BigInt(1) << shift) - 1
    } yield simplifyBitAnd(lhs, Literal(mask.toString), ranges, intDecls)

  private def simplifyShiftRight(
      lhs: Expr,
      rhs: Expr,
      ranges: Map[String, IntRange],
      intDecls: Map[String, Expr]
    ): Expr =
    (lhs, constInt(rhs)) match {
      case (_, Some(0)) =>
        lhs
      case (BinaryExpr(inner, BinaryOperator.>>, innerShift), Some(shift))
          if shift >= 0 && constInt(innerShift).exists(_ >= 0) &&
            rangeOfExpr(inner, ranges, intDecls).exists(_.lo >= 0) =>
        simplifyBinary(inner, BinaryOperator.>>, Literal((constInt(innerShift).get + shift).toString))
      case _ =>
        rangeOfExpr(BinaryExpr(lhs, BinaryOperator.>>, rhs), ranges, intDecls)
          .flatMap(_.singleton)
          .map(v => Literal(v.toString))
          .getOrElse(simplifyBinary(lhs, BinaryOperator.>>, rhs))
    }

  private def simplifyBitAnd(
      lhs: Expr,
      rhs: Expr,
      ranges: Map[String, IntRange],
      intDecls: Map[String, Expr]
    ): Expr =
    (constInt(rhs), rangeOfExpr(lhs, ranges, intDecls)) match {
      case (Some(mask), Some(range))
          if mask >= 0 && range.lo >= 0 && range.hiExclusive <= BigInt(mask) + 1 =>
        lhs
      case _ =>
        rangeOfExpr(BinaryExpr(lhs, BinaryOperator.bitAnd, rhs), ranges, intDecls)
          .flatMap(_.singleton)
          .map(v => Literal(v.toString))
          .getOrElse(simplifyBinary(lhs, BinaryOperator.bitAnd, rhs))
    }

  private def powerOfTwoShift(expr: Expr): Option[Int] =
    constInt(expr)
      .filter(n => n > 1 && (n & (n - 1)) == 0)
      .map(n => Integer.numberOfTrailingZeros(n))

  private def properDivisorsDescending(n: BigInt): Seq[BigInt] =
  {
    val out = scala.collection.mutable.ArrayBuffer.empty[BigInt]
    var i = BigInt(2)
    while (i * i <= n) {
      if (n % i == 0) {
        out += i
        val other = n / i
        if (other != i && other != n) {
          out += other
        }
      }
      i += 1
    }
    out.distinct.sortWith(_ > _).toSeq
  }

  private def floorDivLinearConst(linear: LinearInt, divisor: BigInt): LinearInt = {
    require(linear.terms.isEmpty)
    LinearInt(linear.const / divisor, Map.empty)
  }

  private def positiveMod(value: BigInt, divisor: BigInt): BigInt = {
    val m = value % divisor
    if (m < 0) m + divisor else m
  }

  private def linearOf(
      expr: Expr,
      intDecls: Map[String, Expr],
      seen: Set[String] = Set.empty
    ): Option[LinearInt] =
    expr match {
      case Literal(text) =>
        text.toIntOption.map(v => LinearInt(v, Map.empty))
      case ArithmeticExpr(Cst(value)) =>
        Some(LinearInt(value, Map.empty))
      case DeclRef(name) =>
        if (seen.contains(name)) {
          Some(LinearInt(0, Map(name -> 1)))
        } else {
          intDecls.get(name)
            .flatMap(linearOf(_, intDecls, seen + name))
            .orElse(Some(LinearInt(0, Map(name -> 1))))
        }
      case BinaryExpr(lhs, BinaryOperator.+, rhs) =>
        for { l <- linearOf(lhs, intDecls, seen); r <- linearOf(rhs, intDecls, seen) } yield l + r
      case BinaryExpr(lhs, BinaryOperator.-, rhs) =>
        for { l <- linearOf(lhs, intDecls, seen); r <- linearOf(rhs, intDecls, seen) } yield l - r
      case BinaryExpr(lhs, BinaryOperator.*, rhs) =>
        (constInt(lhs), constInt(rhs)) match {
          case (Some(c), _) => linearOf(rhs, intDecls, seen).map(_ * c)
          case (_, Some(c)) => linearOf(lhs, intDecls, seen).map(_ * c)
          case _ => None
        }
      case _ =>
        None
    }

  private def rangeOf(
      linear: LinearInt,
      ranges: Map[String, IntRange]
    ): Option[IntRange] = {
    var current = IntRange(linear.const, linear.const + 1)
    linear.terms.foreach { case (name, coef) =>
      ranges.get(name) match {
        case Some(range) =>
          current = current + (range * coef)
        case None =>
          return None
      }
    }
    Some(current)
  }

  private def linearToExpr(linear: LinearInt): Expr = {
    val pieces = scala.collection.mutable.ArrayBuffer.empty[Expr]
    if (linear.const != 0) {
      pieces += Literal(linear.const.toString)
    }
    linear.terms.toSeq.sortBy(_._1).foreach { case (name, coef) =>
      if (coef == 1) {
        pieces += DeclRef(name)
      } else if (coef == -1) {
        pieces += BinaryExpr(Literal("0"), BinaryOperator.-, DeclRef(name))
      } else {
        pieces += BinaryExpr(Literal(coef.toString), BinaryOperator.*, DeclRef(name))
      }
    }
    pieces.reduceOption((acc, e) => BinaryExpr(acc, BinaryOperator.+, e))
      .getOrElse(Literal("0"))
  }

  private def stripComments(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        Block(body.filterNot(isComment).map(stripComments))

      case Stmts(a, b) =>
        blockOrStmt(flatten(Stmts(stripComments(a), stripComments(b))).filterNot(isComment))

      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment, stripComments(body).asInstanceOf[Block])

      case WhileLoop(cond, body) =>
        WhileLoop(cond, stripComments(body))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, stripComments(trueBody),
          falseBody.map(stripComments).filterNot(flatten(_).isEmpty))

      case other =>
        other
    }

  private def pruneUnusedScalarDecls(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        val rewritten = body.map(pruneUnusedScalarDecls)
        Block(removeUnusedScalarDecls(rewritten))

      case Stmts(a, b) =>
        blockOrStmt(removeUnusedScalarDecls(flatten(Stmts(
          pruneUnusedScalarDecls(a),
          pruneUnusedScalarDecls(b)
        ))))

      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
          pruneUnusedScalarDecls(body).asInstanceOf[Block])

      case WhileLoop(cond, body) =>
        WhileLoop(cond, pruneUnusedScalarDecls(body))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, pruneUnusedScalarDecls(trueBody), falseBody.map(pruneUnusedScalarDecls))

      case other =>
        other
    }

  private def simplifyStatements(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        Block(combineImmediateAssignments(body.map(simplifyStatements)))

      case Stmts(a, b) =>
        Stmts(simplifyStatements(a), simplifyStatements(b))

      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
          simplifyStatements(body).asInstanceOf[Block])

      case WhileLoop(cond, body) =>
        WhileLoop(cond, simplifyStatements(body))

      case IfThenElse(cond, trueBody, Some(falseBody)) =>
        simplifyExpr(cond) match {
          case c if isOne(c) =>
            simplifyStatements(trueBody)
          case c if isZero(c) =>
            simplifyStatements(falseBody)
          case c =>
            (singleAssignmentWithPureDecls(trueBody), singleAssignmentWithPureDecls(falseBody)) match {
              case (Some((lhs1, rhs1)), Some((lhs2, rhs2))) if lhs1 == lhs2 && pure(lhs1) =>
                ExprStmt(Assignment(lhs1, TernaryExpr(c, rhs1, rhs2)))
              case _ =>
                IfThenElse(c, simplifyStatements(trueBody), Some(simplifyStatements(falseBody)))
            }
        }

      case IfThenElse(cond, trueBody, falseBody) =>
        simplifyExpr(cond) match {
          case c if isOne(c) =>
            simplifyStatements(trueBody)
          case c if isZero(c) =>
            falseBody.map(simplifyStatements).getOrElse(Block(Seq.empty))
          case c =>
            IfThenElse(c, simplifyStatements(trueBody), falseBody.map(simplifyStatements))
        }

      case other =>
        other
    }

  private def unrollSmallConstantLoops(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        Block(body.flatMap(s => flattenUnrolled(unrollSmallConstantLoops(s))))

      case Stmts(a, b) =>
        Stmts(unrollSmallConstantLoops(a), unrollSmallConstantLoops(b))

      case ForLoop(init, cond, increment, body) =>
        loopRange(init.asInstanceOf[DeclStmt], cond) match {
          case Some((name, IntRange(lo, hiExclusive)))
              if lo >= 0 &&
                hiExclusive >= lo &&
                hiExclusive - lo <= MaxSmallLoopUnrollIterations &&
                !containsBarrier(body) &&
                !containsDeclaration(body) =>
            Block((lo until hiExclusive).flatMap { value =>
              val rewritten = unrollSmallConstantLoops(
                replaceDeclRef(body, name, Literal(value.toString)).asInstanceOf[Stmt])
              flattenUnrolled(rewritten)
            })
          case _ =>
            ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
              unrollSmallConstantLoops(body).asInstanceOf[Block])
        }

      case WhileLoop(cond, body) =>
        WhileLoop(cond, unrollSmallConstantLoops(body))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, unrollSmallConstantLoops(trueBody),
          falseBody.map(unrollSmallConstantLoops))

      case other =>
        other
    }

  private def collapseSingletonLocalOwnerLoops(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        Block(body.map(collapseSingletonLocalOwnerLoops))

      case Stmts(a, b) =>
        Stmts(collapseSingletonLocalOwnerLoops(a), collapseSingletonLocalOwnerLoops(b))

      case ForLoop(init, cond, increment, body) =>
        singletonLocalOwnerLoop(init.asInstanceOf[DeclStmt], cond, increment) match {
          case Some((name, dim)) =>
            val collapsedBody = collapseSingletonLocalOwnerLoops(
              replaceDeclRef(body, name, Literal("0")).asInstanceOf[Stmt])
            IfThenElse(
              BinaryExpr(
                FunCall(DeclRef("get_local_id"), Seq(Literal(dim.toString))),
                BinaryOperator.<,
                Literal("1")
              ),
              collapsedBody,
              None
            )
          case None =>
            ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
              collapseSingletonLocalOwnerLoops(body).asInstanceOf[Block])
        }

      case WhileLoop(cond, body) =>
        WhileLoop(cond, collapseSingletonLocalOwnerLoops(body))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, collapseSingletonLocalOwnerLoops(trueBody),
          falseBody.map(collapseSingletonLocalOwnerLoops))

      case other =>
        other
    }

  private case class OwnerGuarded(stmt: Stmt, ownerVars: Set[String])

  private def guardLocalReductionOwners(
      stmt: Stmt,
      wgConfig: Option[(LocalSize, GlobalSize)],
      localNames: Set[String]
    ): Stmt =
    localOwnerGuard(wgConfig).map(g => guardLocalReductionOwners(stmt, g, localNames).stmt)
      .getOrElse(stmt)

  private def guardLocalReductionOwners(
      stmt: Stmt,
      guard: Expr,
      localNames: Set[String]
    ): OwnerGuarded =
    stmt match {
      case Block(body) =>
        val rewritten = body.foldLeft((Vector.empty[Stmt], Set.empty[String])) {
          case ((out, pendingOwnerVars), current) =>
            val r = guardLocalReductionOwners(current, guard, localNames)
            val guarded =
              if (pendingOwnerVars.nonEmpty &&
                  readsAny(r.stmt, pendingOwnerVars) &&
                  writeRootNames(r.stmt).nonEmpty)
                IfThenElse(guard, r.stmt, None)
              else r.stmt
            (out :+ guarded, pendingOwnerVars ++ r.ownerVars)
        }._1
        OwnerGuarded(Block(rewritten), Set.empty)

      case Stmts(a, b) =>
        val block = guardLocalReductionOwners(
          Block(flatten(a) ++ flatten(b)),
          guard,
          localNames)
        block

      case ForLoop(init, cond, increment, body) =>
        val nested = guardLocalReductionOwners(body, guard, localNames)
        val (guardedBody, ownerVars) =
          guardLocalReductionSegments(nested.stmt.asInstanceOf[Block], guard, localNames)
        val loopOwnerVars =
          if (containsBarrier(guardedBody)) writeRootNames(guardedBody)
          else Set.empty[String]
        OwnerGuarded(
          ForLoop(init.asInstanceOf[DeclStmt], cond, increment, guardedBody),
          ownerVars ++ nested.ownerVars ++ loopOwnerVars
        )

      case WhileLoop(cond, body) =>
        val r = guardLocalReductionOwners(body, guard, localNames)
        OwnerGuarded(WhileLoop(cond, r.stmt), r.ownerVars)

      case IfThenElse(cond, trueBody, falseBody) =>
        val t = guardLocalReductionOwners(trueBody, guard, localNames)
        val f = falseBody.map(guardLocalReductionOwners(_, guard, localNames))
        OwnerGuarded(
          IfThenElse(cond, t.stmt, f.map(_.stmt)),
          t.ownerVars ++ f.map(_.ownerVars).getOrElse(Set.empty)
        )

      case other =>
        OwnerGuarded(other, Set.empty)
    }

  private def guardLocalReductionSegments(
      body: Block,
      guard: Expr,
      localNames: Set[String]
    ): (Block, Set[String]) = {
    val stmts = body.body
    val out = Vector.newBuilder[Stmt]
    var ownerVars = Set.empty[String]
    var i = 0
    while (i < stmts.length) {
      out += stmts(i)
      if (containsBarrier(stmts(i))) {
        val nextBarrier = ((i + 1) until stmts.length).find(j => containsBarrier(stmts(j)))
        val end = nextBarrier.getOrElse(stmts.length)
        val segment = stmts.slice(i + 1, end)
        val localWrites = stmts.take(i).flatMap(writeRootNames).toSet
        val segmentReadsLocal = segment.exists(s => readsAny(s, localWrites))
        val segmentOverwritesLocal = segment.exists(s => writeRootNames(s).exists(localWrites))
        val segmentWrites = segment.flatMap(writeRootNames).toSet
        if (segmentReadsLocal)
          ownerVars ++= segmentWrites -- localWrites
        val feedsNextBarrierSegment = nextBarrier.exists { barrierIndex =>
          val start = barrierIndex + 1
          val stop = (start until stmts.length)
            .find(j => containsBarrier(stmts(j)))
            .getOrElse(stmts.length)
          val nextSegment = stmts.slice(start, stop)
          nextSegment.exists(s => readsAny(s, segmentWrites))
        }
        if (
          segment.nonEmpty &&
          segmentWrites.nonEmpty &&
          segmentReadsLocal &&
          !segmentOverwritesLocal &&
          !feedsNextBarrierSegment &&
          segmentWrites.intersect(localNames).isEmpty
        ) {
          val segmentOwnerVars = segment.flatMap(writeRootNames).toSet -- localWrites
          ownerVars ++= segmentOwnerVars
          out += {
            if (segmentAlreadyOwnerGuarded(segment, guard)) blockOrStmt(segment)
            else IfThenElse(guard, blockOrStmt(segment), None)
          }
          i = end - 1
        }
      }
      i += 1
    }
    (Block(out.result()), ownerVars)
  }

  private def segmentAlreadyOwnerGuarded(segment: Seq[Stmt], guard: Expr): Boolean = {
    val requiredDims = localIdZeroGuardDims(guard)
    requiredDims.nonEmpty && segment.forall {
      case IfThenElse(cond, _, falseBody) =>
        falseBody.forall(f => flatten(f).isEmpty) &&
          requiredDims.subsetOf(localIdZeroGuardDims(cond))
      case _ =>
        false
    }
  }

  private def localIdZeroGuardDims(expr: Expr): Set[Int] =
    expr match {
      case BinaryExpr(lhs, BinaryOperator.&&, rhs) =>
        localIdZeroGuardDims(lhs) ++ localIdZeroGuardDims(rhs)
      case BinaryExpr(localIdCall(dim), BinaryOperator.==, rhs)
          if constInt(rhs).contains(0) =>
        Set(dim)
      case BinaryExpr(lhs, BinaryOperator.==, localIdCall(dim))
          if constInt(lhs).contains(0) =>
        Set(dim)
      case _ =>
        Set.empty
    }

  private def localOwnerGuard(wgConfig: Option[(LocalSize, GlobalSize)]): Option[Expr] =
    wgConfig.flatMap { case (LocalSize(local), _) =>
      val dims = (0 to 2).filter(dim => constNat(local(dim)).exists(_ > 1))
      dims.map { dim =>
        BinaryExpr(
          FunCall(DeclRef("get_local_id"), Seq(Literal(dim.toString))),
          BinaryOperator.==,
          Literal("0"))
      }.reduceOption((a, b) => BinaryExpr(a, BinaryOperator.&&, b))
    }

  private def singletonLocalOwnerLoop(
      init: DeclStmt,
      cond: Expr,
      increment: Expr
    ): Option[(String, Int)] =
    (init, cond) match {
      case (
          DeclStmt(VarDecl(name, BasicType("int", _), Some(localIdCall(dim)))),
          BinaryExpr(DeclRef(condName), BinaryOperator.<, one)
        ) if name == condName && constInt(one).contains(1) &&
          incrementsByLocalSize(name, dim, increment) =>
        Some(name -> dim)
      case _ =>
        None
    }

  private object localIdCall {
    def unapply(expr: Expr): Option[Int] =
      expr match {
        case FunCall(DeclRef("get_local_id"), Seq(Literal(text))) =>
          text.toIntOption
        case FunCall(DeclRef("get_local_id"), Seq(ArithmeticExpr(Cst(value)))) =>
          Some(value.toInt)
        case ArithmeticExpr(b: BuiltInFunctionCall)
            if b.toString == s"get_local_id(${b.param})" =>
          Some(b.param)
        case ArithmeticExpr(ae) if ae.toString.startsWith("get_local_id(") =>
          ae.toString.stripPrefix("get_local_id(").stripSuffix(")").toIntOption
        case Literal(text) if text.startsWith("get_local_id(") =>
          text.stripPrefix("get_local_id(").stripSuffix(")").toIntOption
        case _ =>
          None
      }
  }

  private def incrementsByLocalSize(name: String, dim: Int, expr: Expr): Boolean =
    expr match {
      case Assignment(DeclRef(lhs), BinaryExpr(DeclRef(rhs), BinaryOperator.+, localSizeCall(`dim`)))
          if lhs == name && rhs == name => true
      case Assignment(DeclRef(lhs), BinaryExpr(localSizeCall(`dim`), BinaryOperator.+, DeclRef(rhs)))
          if lhs == name && rhs == name => true
      case _ => false
    }

  private object localSizeCall {
    def unapply(expr: Expr): Option[Int] =
      expr match {
        case FunCall(DeclRef("get_local_size"), Seq(Literal(text))) =>
          text.toIntOption
        case FunCall(DeclRef("get_local_size"), Seq(ArithmeticExpr(Cst(value)))) =>
          Some(value.toInt)
        case ArithmeticExpr(b: BuiltInFunctionCall)
            if b.toString == s"get_local_size(${b.param})" =>
          Some(b.param)
        case ArithmeticExpr(ae) if ae.toString.startsWith("get_local_size(") =>
          ae.toString.stripPrefix("get_local_size(").stripSuffix(")").toIntOption
        case Literal(text) if text.startsWith("get_local_size(") =>
          text.stripPrefix("get_local_size(").stripSuffix(")").toIntOption
        case _ =>
          None
      }
  }

  private def collapseSingleIterationLocalIdLoops(
      stmt: Stmt,
      wgConfig: Option[(LocalSize, GlobalSize)]
    ): Stmt = {
    val localExtents =
      wgConfig match {
        case Some((LocalSize(local), _)) =>
          (0 to 2).flatMap(dim => constNat(local(dim)).map(dim -> _)).toMap
        case None =>
          Map.empty[Int, BigInt]
      }

    def rewrite(s: Stmt, ranges: Map[String, IntRange]): Stmt =
      s match {
        case Block(body) =>
          Block(body.map(rewrite(_, ranges)))
        case Stmts(a, b) =>
          Stmts(rewrite(a, ranges), rewrite(b, ranges))
        case ForLoop(init, cond, increment, body) =>
          collapseSingleIterationLocalIdLoop(
            init.asInstanceOf[DeclStmt],
            cond,
            increment,
            body.asInstanceOf[Block],
            localExtents,
            ranges
          ).getOrElse(
            ForLoop(
              init.asInstanceOf[DeclStmt],
              cond,
              increment,
              rewrite(body, loopRange(init.asInstanceOf[DeclStmt], cond)
                .map { case (name, range) => ranges + (name -> range) }
                .getOrElse(ranges)).asInstanceOf[Block])
          )
        case WhileLoop(cond, body) =>
          WhileLoop(cond, rewrite(body, ranges))
        case IfThenElse(cond, trueBody, falseBody) =>
          IfThenElse(cond, rewrite(trueBody, ranges), falseBody.map(rewrite(_, ranges)))
        case other =>
          other
      }

    rewrite(stmt, Map.empty)
  }

  private def collapseSingleIterationLocalIdLoop(
      init: DeclStmt,
      cond: Expr,
      increment: Expr,
      body: Block,
      localExtents: Map[Int, BigInt],
      ranges: Map[String, IntRange]
    ): Option[Stmt] =
    (init, cond) match {
      case (
          DeclStmt(v @ VarDecl(name, BasicType("int", _), Some(localIdCall(dim)))),
          BinaryExpr(DeclRef(condName), BinaryOperator.<, bound)
        ) if name == condName =>
        for {
          localExtent <- localExtents.get(dim)
          if incrementsByFixedLocalExtent(name, dim, localExtent, increment)
          boundRange <- exprRangeWithContext(bound, ranges)
            .orElse(arithmeticExprRange(bound))
            .orElse(constInt(bound).map(n => IntRange(n, n + 1)))
          if boundRange.hiExclusive <= localExtent + 1
        } yield {
          IfThenElse(
            BinaryExpr(localIdExpr(dim), BinaryOperator.<, bound),
            Block(DeclStmt(v) +: body.body),
            None)
        }
      case _ =>
        None
    }

  private def localIdExpr(dim: Int): Expr =
    FunCall(DeclRef("get_local_id"), Seq(Literal(dim.toString)))

  private def incrementsByFixedLocalExtent(
      name: String,
      dim: Int,
      localExtent: BigInt,
      expr: Expr
    ): Boolean =
    incrementsByLocalSize(name, dim, expr) || (expr match {
      case Assignment(DeclRef(lhs), BinaryExpr(DeclRef(rhs), BinaryOperator.+, step))
          if lhs == name && rhs == name =>
        constInt(step).exists(v => BigInt(v) == localExtent)
      case Assignment(DeclRef(lhs), BinaryExpr(step, BinaryOperator.+, DeclRef(rhs)))
          if lhs == name && rhs == name =>
        constInt(step).exists(v => BigInt(v) == localExtent)
      case _ =>
        false
    })

  private def exprRangeWithContext(
      expr: Expr,
      ranges: Map[String, IntRange]
    ): Option[IntRange] =
    expr match {
      case DeclRef(name) =>
        ranges.get(name)
      case Literal(text) =>
        text.toIntOption.map(v => IntRange(v, BigInt(v) + 1))
      case UnaryExpr(UnaryOperator.-, e) =>
        exprRangeWithContext(e, ranges).map(r => IntRange(-(r.hiExclusive - 1), -r.lo + 1))
      case BinaryExpr(lhs, BinaryOperator.+, rhs) =>
        for { l <- exprRangeWithContext(lhs, ranges); r <- exprRangeWithContext(rhs, ranges) } yield l + r
      case BinaryExpr(lhs, BinaryOperator.-, rhs) =>
        for { l <- exprRangeWithContext(lhs, ranges); r <- exprRangeWithContext(rhs, ranges) } yield l + IntRange(-(r.hiExclusive - 1), -r.lo + 1)
      case BinaryExpr(lhs, BinaryOperator.*, rhs) =>
        (constInt(lhs), exprRangeWithContext(rhs, ranges)) match {
          case (Some(c), Some(r)) => Some(r * BigInt(c))
          case _ => (exprRangeWithContext(lhs, ranges), constInt(rhs)) match {
            case (Some(l), Some(c)) => Some(l * BigInt(c))
            case _ => None
          }
        }
      case BinaryExpr(lhs, BinaryOperator.<<, rhs) =>
        for {
          base <- constInt(lhs)
          exponent <- exprRangeWithContext(rhs, ranges)
          if base > 0 && exponent.lo >= 0 && exponent.hiExclusive <= 31
        } yield {
          val values = (exponent.lo until exponent.hiExclusive)
            .map(e => BigInt(base) << e.toInt)
          IntRange(values.min, values.max + 1)
        }
      case BinaryExpr(lhs, BinaryOperator.>>, rhs) =>
        for {
          base <- exprRangeWithContext(lhs, ranges)
          shift <- constInt(rhs)
          if base.lo >= 0 && shift >= 0
        } yield IntRange(base.lo >> shift, ((base.hiExclusive - 1) >> shift) + 1)
      case BinaryExpr(_, BinaryOperator.bitAnd, rhs) =>
        constInt(rhs)
          .filter(_ >= 0)
          .map(mask => IntRange(0, BigInt(mask) + 1))
      case _ =>
        arithmeticExprRange(expr)
    }

  private def mergeAdjacentIndependentForLoops(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        Block(mergeAdjacentIndependentForLoopsInBlock(
          body.map(mergeAdjacentIndependentForLoops)))

      case Stmts(a, b) =>
        blockOrStmt(mergeAdjacentIndependentForLoopsInBlock(flatten(Stmts(
          mergeAdjacentIndependentForLoops(a),
          mergeAdjacentIndependentForLoops(b)
        ))))

      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
          mergeAdjacentIndependentForLoops(body).asInstanceOf[Block])

      case WhileLoop(cond, body) =>
        WhileLoop(cond, mergeAdjacentIndependentForLoops(body))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, mergeAdjacentIndependentForLoops(trueBody),
          falseBody.map(mergeAdjacentIndependentForLoops))

      case other =>
        other
    }

  private def mergeAdjacentIndependentForLoopsInBlock(stmts: Seq[Stmt]): Seq[Stmt] = {
    val out = scala.collection.mutable.ArrayBuffer.empty[Stmt]
    var i = 0
    while (i < stmts.length) {
      if (i + 1 < stmts.length) {
        mergeForLoops(stmts(i), stmts(i + 1)) match {
          case Some(loop) =>
            out += loop
            i += 2
          case None =>
            out += stmts(i)
            i += 1
        }
      } else {
        out += stmts(i)
        i += 1
      }
    }
    out.toSeq
  }

  private def mergeForLoops(a: Stmt, b: Stmt): Option[ForLoop] =
    (a, b) match {
      case (
          f1 @ ForLoop(init1, cond1, inc1, body1),
          ForLoop(init2, cond2, inc2, body2)
        ) =>
        val initDecl1 = init1.asInstanceOf[DeclStmt]
        val initDecl2 = init2.asInstanceOf[DeclStmt]
        val block1 = body1.asInstanceOf[Block]
        val block2 = body2.asInstanceOf[Block]
        for {
          (name1, range1) <- loopRange(initDecl1, cond1)
          (name2, range2) <- loopRange(initDecl2, cond2)
          if range1 == range2
          if unitIncrement(name1, inc1) && unitIncrement(name2, inc2)
          if !containsDeclaration(block1) && !containsDeclaration(block2)
          if !containsBarrier(block1) && !containsBarrier(block2)
          if independentLoopBodies(block1, block2)
          if accumulatorMergeKeepsRegisterPressure(block1, block2)
        } yield {
          val renamedBody2 =
            replaceDeclRef(block2, name2, DeclRef(name1)).asInstanceOf[Block]
          ForLoop(
            initDecl1,
            cond1,
            inc1,
            Block(block1.body ++ renamedBody2.body)
          )
        }
      case _ =>
        None
    }

  private def unitIncrement(name: String, increment: Expr): Boolean = {
    val compact = C.AST.Printer(increment).replace(" ", "")
    compact == s"$name++" ||
      compact == s"$name=$name+1" ||
      compact == s"$name=1+$name"
  }

  private def independentLoopBodies(lhs: Stmt, rhs: Stmt): Boolean = {
    val lhsWrites = assignedNames(lhs)
    val rhsWrites = assignedNames(rhs)
    val lhsReads = readNames(lhs)
    val rhsReads = readNames(rhs)
    lhsWrites.intersect(rhsReads).isEmpty &&
      rhsWrites.intersect(lhsReads).isEmpty &&
      lhsWrites.intersect(rhsWrites).isEmpty
  }

  private def accumulatorMergeKeepsRegisterPressure(lhs: Stmt, rhs: Stmt): Boolean = {
    val lhsAcc = accumulatorUpdateNames(lhs)
    val rhsAcc = accumulatorUpdateNames(rhs)
    lhsAcc.isEmpty || rhsAcc.isEmpty ||
      lhsAcc.union(rhsAcc).size <= MaxMergedAccumulatorAssignments
  }

  private def accumulatorUpdateNames(stmt: Stmt): Set[String] = {
    val names = scala.collection.mutable.Set.empty[String]

    def loop(s: Stmt): Unit =
      s match {
        case ExprStmt(Assignment(DeclRef(name), rhs)) if collectDeclRefs(rhs).contains(name) =>
          names += name
        case Block(body) =>
          body.foreach(loop)
        case Stmts(a, b) =>
          loop(a); loop(b)
        case IfThenElse(_, trueBody, falseBody) =>
          loop(trueBody); falseBody.foreach(loop)
        case _ =>
      }

    loop(stmt)
    names.toSet
  }

  private def guardLoopTailLocalBarriers(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        Block(body.map(guardLoopTailLocalBarriers))

      case Stmts(a, b) =>
        Stmts(guardLoopTailLocalBarriers(a), guardLoopTailLocalBarriers(b))

      case ForLoop(init, cond, increment, body) =>
        val initDecl = init.asInstanceOf[DeclStmt]
        val rewrittenBody = guardLoopTailLocalBarriers(body).asInstanceOf[Block]
        val guardedBody =
          (loopRange(initDecl, cond), rewrittenBody.body.lastOption) match {
            case (Some((name, IntRange(lo, hiExclusive))), Some(last))
                if hiExclusive > lo + 1 && unitIncrement(name, increment) && isLocalBarrier(last) =>
              Block(rewrittenBody.body.dropRight(1) :+
                IfThenElse(
                  BinaryExpr(DeclRef(name), BinaryOperator.<, Literal((hiExclusive - 1).toString)),
                  last,
                  None))
            case _ =>
              rewrittenBody
          }
        ForLoop(initDecl, cond, increment, guardedBody)

      case WhileLoop(cond, body) =>
        WhileLoop(cond, guardLoopTailLocalBarriers(body))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, guardLoopTailLocalBarriers(trueBody),
          falseBody.map(guardLoopTailLocalBarriers))

      case other =>
        other
    }

  private def hoistLoopInvariantPrefixes(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        Block(body.map(hoistLoopInvariantPrefixes))

      case Stmts(a, b) =>
        Stmts(hoistLoopInvariantPrefixes(a), hoistLoopInvariantPrefixes(b))

      case ForLoop(init, cond, increment, body) =>
        val initDecl = init.asInstanceOf[DeclStmt]
        val loopName = initDecl.decl.name
        val loopBody = hoistLoopInvariantPrefixes(body).asInstanceOf[Block]
        val stmts = loopBody.body
        val loopIsStaticallyPositive = loopRange(initDecl, cond) match {
          case Some((name, IntRange(lo, hiExclusive))) =>
            name == loopName && hiExclusive > lo && unitIncrement(loopName, increment)
          case _ =>
            false
        }
        val prefixLen = hoistableLoopInvariantPrefixLength(
          stmts,
          loopName,
          loopIsStaticallyPositive)
        val suffixAssigned = stmts.drop(prefixLen).flatMap(assignedNames).toSet
        var safePrefixLen = prefixLen
        while (safePrefixLen > 0 &&
            assignedNames(stmts(safePrefixLen - 1)).exists(suffixAssigned)) {
          safePrefixLen -= 1
        }

        if (safePrefixLen == 0) {
          ForLoop(initDecl, cond, increment, loopBody)
        } else {
          Block(stmts.take(safePrefixLen) :+
            ForLoop(
              initDecl,
              cond,
              increment,
              Block(stmts.drop(safePrefixLen))))
        }

      case WhileLoop(cond, body) =>
        WhileLoop(cond, hoistLoopInvariantPrefixes(body))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, hoistLoopInvariantPrefixes(trueBody),
          falseBody.map(hoistLoopInvariantPrefixes))

      case other =>
        other
    }

  private def hoistableLoopInvariantPrefixLength(
      stmts: Seq[Stmt],
      loopName: String,
      loopIsStaticallyPositive: Boolean
    ): Int = {
    var idx = 0
    var continue = true

    while (idx < stmts.length && continue) {
      val stmt = stmts(idx)
      if (referencesName(stmt, loopName) || containsBarrier(stmt)) {
        continue = false
      } else {
        stmt match {
          case DeclStmt(VarDecl(_, t, None)) if hoistablePrivateType(t) =>
            idx += 1

          case Block(body) if body.forall(hoistableLoopInvariantStmt(_, loopName)) =>
            idx += 1

          case Stmts(a, b)
              if hoistableLoopInvariantStmt(a, loopName) &&
                 hoistableLoopInvariantStmt(b, loopName) =>
            idx += 1

          case _ =>
            continue = false
        }
      }
    }

    idx
  }

  private def hoistableInvariantAssignment(
      name: String,
      rhs: Expr,
      initializedInPrefix: Set[String]
    ): Boolean = {
    val refs = collectDeclRefs(rhs)
    !refs.contains(name) || initializedInPrefix.contains(name)
  }

  private def flattenUnrolled(stmt: Stmt): Seq[Stmt] =
    stmt match {
      case Block(body) => body
      case other => Seq(other)
    }

  private def flattenTrivialBlocks(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        Block(body.flatMap { s =>
          flattenBlockStmt(flattenTrivialBlocks(s))
        })

      case Stmts(a, b) =>
        blockOrStmt(flatten(Stmts(
          flattenTrivialBlocks(a),
          flattenTrivialBlocks(b)
        )))

      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
          flattenTrivialBlocks(body).asInstanceOf[Block])

      case WhileLoop(cond, body) =>
        WhileLoop(cond, flattenTrivialBlocks(body))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, flattenTrivialBlocks(trueBody),
          falseBody.map(flattenTrivialBlocks))

      case other =>
        other
    }

  private def mergeAdjacentIdenticalIfs(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        Block(mergeAdjacentIdenticalIfsInBlock(body.map(mergeAdjacentIdenticalIfs)))

      case Stmts(a, b) =>
        blockOrStmt(mergeAdjacentIdenticalIfsInBlock(flatten(Stmts(
          mergeAdjacentIdenticalIfs(a),
          mergeAdjacentIdenticalIfs(b)
        ))))

      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
          mergeAdjacentIdenticalIfs(body).asInstanceOf[Block])

      case WhileLoop(cond, body) =>
        WhileLoop(cond, mergeAdjacentIdenticalIfs(body))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, mergeAdjacentIdenticalIfs(trueBody),
          falseBody.map(mergeAdjacentIdenticalIfs))

      case other =>
        other
    }

  private def mergeAdjacentIdenticalIfsInBlock(stmts: Seq[Stmt]): Seq[Stmt] = {
    val out = Vector.newBuilder[Stmt]
    var i = 0
    while (i < stmts.length) {
      stmts(i) match {
        case IfThenElse(cond, trueBody, None) if !containsDeclaration(trueBody) =>
          val merged = Vector.newBuilder[Stmt]
          var j = i
          var keepMerging = true
          while (j < stmts.length && keepMerging) {
            stmts(j) match {
              case IfThenElse(`cond`, body, None) if !containsDeclaration(body) =>
                merged ++= flatten(body)
                j += 1
              case _ =>
                keepMerging = false
            }
          }
          val body = merged.result()
          if (body.nonEmpty) {
            out += IfThenElse(cond, blockOrStmt(body), None)
          }
          i = math.max(i + 1, j)

        case other =>
          out += other
          i += 1
      }
    }
    out.result()
  }

  private def collapseNestedIdenticalIfs(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        Block(body.map(collapseNestedIdenticalIfs))

      case Stmts(a, b) =>
        Stmts(collapseNestedIdenticalIfs(a), collapseNestedIdenticalIfs(b))

      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
          collapseNestedIdenticalIfs(body).asInstanceOf[Block])

      case WhileLoop(cond, body) =>
        WhileLoop(cond, collapseNestedIdenticalIfs(body))

      case IfThenElse(cond, IfThenElse(innerCond, trueBody, None), None)
          if sameCondition(cond, innerCond) =>
        collapseNestedIdenticalIfs(IfThenElse(cond, trueBody, None))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, collapseNestedIdenticalIfs(trueBody),
          falseBody.map(collapseNestedIdenticalIfs))

      case other =>
        other
    }

  private def sameCondition(lhs: Expr, rhs: Expr): Boolean =
    C.AST.Printer(lhs).replace(" ", "") == C.AST.Printer(rhs).replace(" ", "")

  private def mergeInitialAssignmentsIntoDecls(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        Block(mergeInitialAssignmentsInBlock(body.map(mergeInitialAssignmentsIntoDecls)))

      case Stmts(a, b) =>
        blockOrStmt(mergeInitialAssignmentsInBlock(flatten(Stmts(
          mergeInitialAssignmentsIntoDecls(a),
          mergeInitialAssignmentsIntoDecls(b)
        ))))

      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
          mergeInitialAssignmentsIntoDecls(body).asInstanceOf[Block])

      case WhileLoop(cond, body) =>
        WhileLoop(cond, mergeInitialAssignmentsIntoDecls(body))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, mergeInitialAssignmentsIntoDecls(trueBody),
          falseBody.map(mergeInitialAssignmentsIntoDecls))

      case other =>
        other
    }

  private def mergeInitialAssignmentsInBlock(stmts: Seq[Stmt]): Seq[Stmt] = {
    val out = scala.collection.mutable.ArrayBuffer.empty[Stmt]
    val pending = scala.collection.mutable.Map.empty[String, Int]

    stmts.foreach {
      case d @ DeclStmt(VarDecl(name, _, None)) =>
        pending(name) = out.length
        out += d

      case ExprStmt(Assignment(DeclRef(name), rhs))
          if pending.contains(name) && !collectDeclRefs(rhs).contains(name) =>
        out(pending(name)) match {
          case DeclStmt(v @ VarDecl(`name`, _, None)) =>
            out(pending(name)) = DeclStmt(withInit(v, Some(rhs)))
          case _ =>
            out += ExprStmt(Assignment(DeclRef(name), rhs))
        }
        pending -= name

      case other =>
        pending.clear()
        out += other
    }

    out.toSeq
  }

  private def mergeAdjacentPureDeclBlocks(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        Block(mergePureDeclBlocks(body.map(mergeAdjacentPureDeclBlocks)))

      case Stmts(a, b) =>
        blockOrStmt(mergePureDeclBlocks(flatten(Stmts(
          mergeAdjacentPureDeclBlocks(a),
          mergeAdjacentPureDeclBlocks(b)
        ))))

      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
          mergeAdjacentPureDeclBlocks(body).asInstanceOf[Block])

      case WhileLoop(cond, body) =>
        WhileLoop(cond, mergeAdjacentPureDeclBlocks(body))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, mergeAdjacentPureDeclBlocks(trueBody),
          falseBody.map(mergeAdjacentPureDeclBlocks))

      case other =>
        other
    }

  private def mergePureDeclBlocks(stmts: Seq[Stmt]): Seq[Stmt] = {
    val out = scala.collection.mutable.ArrayBuffer.empty[Stmt]
    stmts.foreach { stmt =>
      (out.lastOption, mergeablePureDeclBlocks(out.lastOption, stmt)) match {
        case (Some(_), Some(merged)) =>
          out.remove(out.length - 1)
          out += merged
        case _ =>
          out += stmt
      }
    }
    out.toSeq
  }

  private def mergeablePureDeclBlocks(lhsOpt: Option[Stmt], rhs: Stmt): Option[Stmt] =
    (lhsOpt, rhs) match {
      case (Some(Block(lhs)), Block(rhsBody)) =>
        for {
          (lhsDecls, lhsRest) <- pureDeclPrefix(lhs)
          (rhsDecls, rhsRest) <- pureDeclPrefix(rhsBody)
          if lhsDecls.nonEmpty && lhsDecls == rhsDecls
        } yield Block(lhsDecls ++ lhsRest ++ rhsRest)
      case _ =>
        None
    }

  private def pureDeclPrefix(stmts: Seq[Stmt]): Option[(Seq[Stmt], Seq[Stmt])] = {
    val prefix = stmts.takeWhile {
      case DeclStmt(VarDecl(_, _: C.AST.BasicType, Some(init))) if pure(init) => true
      case _ => false
    }
    if (prefix.isEmpty) {
      None
    } else {
      Some(prefix -> stmts.drop(prefix.length))
    }
  }

  private def forwardScalarAccumulatorCopies(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        Block(forwardScalarAccumulatorCopiesInBlock(body.map(forwardScalarAccumulatorCopies)))

      case Stmts(a, b) =>
        blockOrStmt(forwardScalarAccumulatorCopiesInBlock(flatten(Stmts(
          forwardScalarAccumulatorCopies(a),
          forwardScalarAccumulatorCopies(b)
        ))))

      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
          forwardScalarAccumulatorCopies(body).asInstanceOf[Block])

      case WhileLoop(cond, body) =>
        WhileLoop(cond, forwardScalarAccumulatorCopies(body))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, forwardScalarAccumulatorCopies(trueBody),
          falseBody.map(forwardScalarAccumulatorCopies))

      case other =>
        other
    }

  private def forwardScalarAccumulatorCopiesInBlock(stmts: Seq[Stmt]): Seq[Stmt] = {
    var current = stmts
    var changed = true
    while (changed) {
      changed = false
      var i = 0
      while (!changed && i < current.length) {
        scalarCopyIn(current(i)) match {
          case Some((tmp, root)) =>
            scalarCopyOutIndex(current, start = i + 1, tmp, root) match {
              case Some(j)
                  if (declaresScalarCopy(current(i), tmp) ||
                    declaredScalarWithoutInitBefore(current, i, tmp)) &&
                    !referencesName(current.take(i), tmp) &&
                    !referencesName(current.slice(i + 1, j), root) &&
                    !writesName(current.slice(i + 1, j), root) &&
                    !referencesName(current.drop(j + 1), tmp) =>
                val middle = current.slice(i + 1, j)
                  .map(replaceDeclRef(_, tmp, DeclRef(root)))
                val next =
                  current.take(i) ++ middle ++ current.drop(j + 1)
                current = removeUnreferencedNoInitDecl(next, tmp)
                changed = true
              case _ =>
                i += 1
            }
          case None =>
            i += 1
        }
      }
    }
    current
  }

  private def forwardSingleAssignmentTemps(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        Block(forwardSingleAssignmentTempsInBlock(body.map(forwardSingleAssignmentTemps)))

      case Stmts(a, b) =>
        blockOrStmt(forwardSingleAssignmentTempsInBlock(flatten(Stmts(
          forwardSingleAssignmentTemps(a),
          forwardSingleAssignmentTemps(b)
        ))))

      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
          forwardSingleAssignmentTemps(body).asInstanceOf[Block])

      case WhileLoop(cond, body) =>
        WhileLoop(cond, forwardSingleAssignmentTemps(body))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, forwardSingleAssignmentTemps(trueBody),
          falseBody.map(forwardSingleAssignmentTemps))

      case other =>
        other
    }

  private def forwardSingleAssignmentTempsInBlock(stmts: Seq[Stmt]): Seq[Stmt] = {
    var current = stmts
    var changed = true
    while (changed) {
      changed = false
      var i = 0
      while (!changed && i < current.length) {
        current(i) match {
          case ExprStmt(Assignment(DeclRef(tmp), rhs))
              if pure(rhs) && !referencesName(rhs, tmp) =>
            val deps = collectDeclRefs(rhs)
            val target = (i + 1 until current.length).find {
              j => current(j) match {
                case ExprStmt(Assignment(_, DeclRef(`tmp`))) => true
                case _ => false
              }
            }
            target match {
              case Some(j)
                  if !referencesName(current.slice(i + 1, j), tmp) &&
                    !writesName(current.slice(i + 1, j), tmp) &&
                    !current.slice(i + 1, j).exists(s => writeRootNames(s).exists(deps)) &&
                    !referencesName(current.drop(j + 1), tmp) =>
                val replacement = current(j) match {
                  case ExprStmt(Assignment(lhs, DeclRef(`tmp`))) =>
                    ExprStmt(Assignment(lhs, rhs))
                }
                current = current.take(i) ++ current.slice(i + 1, j) ++
                  Seq(replacement) ++ current.drop(j + 1)
                changed = true
              case _ =>
                i += 1
            }
          case _ =>
            i += 1
        }
      }
    }
    current
  }

  private def scalarCopyIn(stmt: Stmt): Option[(String, String)] =
    stmt match {
      case DeclStmt(VarDecl(tmp, _: C.AST.BasicType, Some(DeclRef(root))))
          if tmp != root =>
        Some(tmp -> root)
      case ExprStmt(Assignment(DeclRef(tmp), DeclRef(root))) if tmp != root =>
        Some(tmp -> root)
      case _ =>
        None
    }

  private def declaresScalarCopy(stmt: Stmt, name: String): Boolean =
    stmt match {
      case DeclStmt(VarDecl(`name`, _: C.AST.BasicType, Some(_))) => true
      case _ => false
    }

  private def scalarCopyOutIndex(
      stmts: Seq[Stmt],
      start: Int,
      tmp: String,
      root: String
    ): Option[Int] =
    (start until stmts.length).find { index =>
      stmts(index) match {
        case ExprStmt(Assignment(DeclRef(`root`), DeclRef(`tmp`))) => true
        case _ => false
      }
    }

  private def declaredScalarWithoutInitBefore(
      stmts: Seq[Stmt],
      endExclusive: Int,
      name: String
    ): Boolean =
    stmts.take(endExclusive).exists {
      case DeclStmt(VarDecl(`name`, _: C.AST.BasicType, None)) => true
      case _ => false
    }

  private def removeUnreferencedNoInitDecl(stmts: Seq[Stmt], name: String): Seq[Stmt] =
    if (referencesName(stmts, name)) {
      stmts
    } else {
      stmts.filterNot {
        case DeclStmt(VarDecl(`name`, _: C.AST.BasicType, None)) => true
        case _ => false
      }
    }

  private def flattenBlockStmt(stmt: Stmt): Seq[Stmt] =
    stmt match {
      case Block(Seq(single)) if !containsDeclaration(single) =>
        Seq(single)
      case Block(body) if !containsDeclaration(stmt) =>
        body
      case other =>
        Seq(other)
    }

  private def containsDeclaration(stmt: Stmt): Boolean = {
    var found = false
    Nodes.VisitAndRebuild(stmt, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result = {
        n match {
          case _: VarDecl | _: ParamDecl =>
            found = true
            Stop(n)
          case _ =>
            Continue(n, this)
        }
      }
    })
    found
  }

  private def containsBarrier(stmt: Stmt): Boolean = {
    var found = false
    Nodes.VisitAndRebuild(stmt, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result = {
        n match {
          case shine.OpenCL.AST.Barrier(_, _) =>
            found = true
            Stop(n)
          case FunCall(DeclRef("barrier"), _) =>
            found = true
            Stop(n)
          case _ =>
            Continue(n, this)
        }
      }
    })
    found
  }

  private def isLocalBarrier(stmt: Stmt): Boolean =
    stmt match {
      case shine.OpenCL.AST.Barrier(true, false) => true
      case _ => false
    }

  private def isLocalBarrierOnly(stmt: Stmt): Boolean =
    stmt match {
      case s if isLocalBarrier(s) => true
      case IfThenElse(_, trueBody, None) =>
        val body = flatten(trueBody)
        body.nonEmpty && body.forall(isLocalBarrier)
      case _ => false
    }

  private def prunePrivateBookkeepingBarriers(stmt: Stmt, localNames: Set[String]): Stmt =
    if (localNames.isEmpty) {
      stmt
    } else {
      stmt match {
        case Block(body) =>
          Block(prunePrivateBookkeepingBarrierBlock(
            body.map(prunePrivateBookkeepingBarriers(_, localNames)),
            localNames
          ))
        case Stmts(a, b) =>
          blockOrStmt(prunePrivateBookkeepingBarrierBlock(
            flatten(Stmts(
              prunePrivateBookkeepingBarriers(a, localNames),
              prunePrivateBookkeepingBarriers(b, localNames)
            )),
            localNames
          ))
        case ForLoop(init, cond, increment, body) =>
          ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
            prunePrivateBookkeepingBarriers(body, localNames).asInstanceOf[Block])
        case WhileLoop(cond, body) =>
          WhileLoop(cond, prunePrivateBookkeepingBarriers(body, localNames))
        case IfThenElse(cond, trueBody, falseBody) =>
          IfThenElse(cond,
            prunePrivateBookkeepingBarriers(trueBody, localNames),
            falseBody.map(prunePrivateBookkeepingBarriers(_, localNames)))
        case other =>
          other
      }
    }

  private def prunePrivateBookkeepingBarrierBlock(
      stmts: Seq[Stmt],
      localNames: Set[String]
    ): Seq[Stmt] = {
    val out = scala.collection.mutable.ArrayBuffer.empty[Stmt]
    var barrierWithOnlyPrivateBookkeepingAfter = false
    stmts.foreach { stmt =>
      if (isLocalBarrierOnly(stmt) && barrierWithOnlyPrivateBookkeepingAfter) {
        // The preceding barrier already synchronized local memory, and the
        // intervening statements only update private pointer/scalar bookkeeping.
      } else {
        out += stmt
        if (isLocalBarrierOnly(stmt)) {
          barrierWithOnlyPrivateBookkeepingAfter = true
        } else if (touchesLocalStorage(stmt, localNames) || containsBarrier(stmt)) {
          barrierWithOnlyPrivateBookkeepingAfter = false
        }
      }
    }
    out.toSeq
  }

  private def touchesLocalStorage(stmt: Stmt, localNames: Set[String]): Boolean = {
    var found = false
    Nodes.VisitAndRebuild(stmt, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result =
        n match {
          case sub @ ArraySubscript(_, _) if lvalueRoot(sub).exists(localNames) =>
            found = true
            Stop(n)
          case _ =>
            Continue(n, this)
        }
    })
    found
  }

  private case class LocalEffects(reads: Set[String] = Set.empty, writes: Set[String] = Set.empty) {
    def ++(other: LocalEffects): LocalEffects =
      LocalEffects(reads ++ other.reads, writes ++ other.writes)
  }

  private def localMemoryNames(body: Stmt, kernelParams: Seq[ParamDecl]): Set[String] = {
    val names = scala.collection.mutable.Set.empty[String]
    kernelParams.foreach {
      case ParamDecl(name, shine.OpenCL.AST.PointerType(AddressSpace.Local, _, _)) =>
        names += name
      case _ =>
    }
    Nodes.VisitAndRebuild(body, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result = {
        n match {
          case DeclStmt(shine.OpenCL.AST.VarDecl(name, _, AddressSpace.Local, _)) =>
            names += name
          case DeclStmt(shine.OpenCL.AST.VarDecl(name, shine.OpenCL.AST.PointerType(AddressSpace.Local, _, _), _, _)) =>
            names += name
          case _ =>
        }
        Continue(n, this)
      }
    })
    names.toSet
  }

  private def hoistIndependentLocalWriteBarrierRuns(stmt: Stmt, localNames: Set[String]): Stmt =
    if (localNames.isEmpty) {
      stmt
    } else {
      stmt match {
        case Block(body) =>
          Block(hoistIndependentLocalWriteBarrierRunsInBlock(
            body.map(hoistIndependentLocalWriteBarrierRuns(_, localNames)),
            localNames
          ))
        case Stmts(a, b) =>
          blockOrStmt(hoistIndependentLocalWriteBarrierRunsInBlock(
            flatten(Stmts(
              hoistIndependentLocalWriteBarrierRuns(a, localNames),
              hoistIndependentLocalWriteBarrierRuns(b, localNames)
            )),
            localNames
          ))
        case ForLoop(init, cond, increment, body) =>
          ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
            hoistIndependentLocalWriteBarrierRuns(body, localNames).asInstanceOf[Block])
        case WhileLoop(cond, body) =>
          WhileLoop(cond, hoistIndependentLocalWriteBarrierRuns(body, localNames))
        case IfThenElse(cond, trueBody, falseBody) =>
          IfThenElse(
            cond,
            hoistIndependentLocalWriteBarrierRuns(trueBody, localNames),
            falseBody.map(hoistIndependentLocalWriteBarrierRuns(_, localNames))
          )
        case other =>
          other
      }
    }

  private def hoistIndependentLocalWriteBarrierRunsInBlock(
      stmts: Seq[Stmt],
      localNames: Set[String]
    ): Seq[Stmt] = {
    val flat = stmts.flatMap(flatten)
    val out = scala.collection.mutable.ArrayBuffer.empty[Stmt]
    var i = 0
    while (i < flat.length) {
      collectLocalWriteBarrierRun(flat, i, localNames) match {
        case Some((rewritten, next)) =>
          out ++= rewritten
          i = next
        case None =>
          out += flat(i)
          i += 1
      }
    }
    out.toSeq
  }

  private def collectLocalWriteBarrierRun(
      stmts: Seq[Stmt],
      start: Int,
      localNames: Set[String]
    ): Option[(Seq[Stmt], Int)] = {
    if (!isLocalWriteBarrierCandidate(stmts, start, localNames)) {
      return None
    }

    val writes = scala.collection.mutable.ArrayBuffer(stmts(start))
    val segments = scala.collection.mutable.ArrayBuffer.empty[Seq[Stmt]]
    var cursor = start
    var keepGoing = true

    while (keepGoing) {
      val segmentStart = cursor + 2
      nextLocalWriteBarrierCandidate(stmts, segmentStart, localNames) match {
        case Some(nextIndex) =>
          val segment = stmts.slice(segmentStart, nextIndex)
          val priorEffects =
            (writes.toSeq ++ segments.flatten).foldLeft(LocalEffects()) {
              case (acc, s) => acc ++ localEffects(s, localNames)
            }
          val nextWriteEffects = localEffects(stmts(nextIndex), localNames)
          if (segment.nonEmpty && independentLocalEffects(priorEffects, nextWriteEffects)) {
            segments += segment
            writes += stmts(nextIndex)
            cursor = nextIndex
          } else {
            keepGoing = false
          }
        case None =>
          keepGoing = false
      }
    }

    if (writes.length < 2) {
      None
    } else {
      val tailStart = cursor + 2
      val tailEnd = nextLocalWriteBarrierCandidate(stmts, tailStart, localNames)
        .getOrElse(stmts.length)
      segments += stmts.slice(tailStart, tailEnd)
      Some((writes.toSeq ++ Seq(shine.OpenCL.AST.Barrier(local = true, global = false)) ++ segments.flatten, tailEnd))
    }
  }

  private def nextLocalWriteBarrierCandidate(
      stmts: Seq[Stmt],
      start: Int,
      localNames: Set[String]
    ): Option[Int] = {
    var i = start
    while (i < stmts.length) {
      if (isLocalWriteBarrierCandidate(stmts, i, localNames)) {
        return Some(i)
      }
      i += 1
    }
    None
  }

  private def isLocalWriteBarrierCandidate(
      stmts: Seq[Stmt],
      index: Int,
      localNames: Set[String]
    ): Boolean =
    index + 1 < stmts.length &&
      isLocalBarrier(stmts(index + 1)) &&
      isSingleLocalArrayWrite(stmts(index), localNames)

  private def isSingleLocalArrayWrite(stmt: Stmt, localNames: Set[String]): Boolean =
    stmt match {
      case ExprStmt(Assignment(lhs @ ArraySubscript(_, _), _)) =>
        lvalueRoot(lhs).exists(localNames)
      case _ =>
        false
    }

  private def localEffects(stmt: Stmt, localNames: Set[String]): LocalEffects =
    LocalEffects(
      reads = readNames(stmt).intersect(localNames),
      writes = writeRootNames(stmt).intersect(localNames)
    )

  private def independentLocalEffects(a: LocalEffects, b: LocalEffects): Boolean =
    a.writes.intersect(b.reads).isEmpty &&
      a.reads.intersect(b.writes).isEmpty &&
      a.writes.intersect(b.writes).isEmpty

  private def hoistableLoopInvariantStmt(stmt: Stmt, loopName: String): Boolean =
    !referencesName(stmt, loopName) && !containsBarrier(stmt) && (stmt match {
      case DeclStmt(VarDecl(_, t, None)) =>
        hoistablePrivateType(t)
      case ExprStmt(Assignment(DeclRef(_), _)) =>
        false
      case Block(body) =>
        body.forall(hoistableLoopInvariantStmt(_, loopName))
      case Stmts(a, b) =>
        hoistableLoopInvariantStmt(a, loopName) &&
          hoistableLoopInvariantStmt(b, loopName)
      case _ =>
        false
    })

  private def hoistablePrivateType(t: Type): Boolean =
    t match {
      case _: C.AST.ArrayType | _: C.AST.PointerType => false
      case _ => true
    }

  private def assignedNames(stmt: Stmt): Set[String] = {
    val names = scala.collection.mutable.Set.empty[String]
    Nodes.VisitAndRebuild(stmt, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result =
        n match {
          // A declaration with an initializer writes the variable at this
          // lexical point.  Treating it as a pure declaration is unsafe for
          // loop-prefix hoisting: reduce accumulators such as `float16 acc =
          // 0` must be reinitialized for every enclosing map/loop iteration.
          case DeclStmt(OpenCL.AST.VarDecl(name, _, _, Some(_))) =>
            names += name
            Continue(n, this)
          case DeclStmt(VarDecl(name, _, Some(_))) =>
            names += name
            Continue(n, this)
          case Assignment(lhs, _) =>
            lvalueRoot(lhs).foreach(names += _)
            Continue(n, this)
          case _ =>
            Continue(n, this)
        }
    })
    names.toSet
  }

  private def replaceDeclRef(stmt: Stmt, name: String, replacement: Expr): Stmt =
    Nodes.VisitAndRebuild(stmt, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result = {
        n match {
          case DeclRef(nm) if nm == name =>
            Stop(replacement)
          case _ =>
            Continue(n, this)
        }
      }
    })

  private def combineImmediateAssignments(stmts: Seq[Stmt]): Seq[Stmt] = {
    val out = scala.collection.mutable.ArrayBuffer.empty[Stmt]
    var i = 0
    while (i < stmts.length) {
      if (i + 1 < stmts.length) {
        (stmts(i), stmts(i + 1)) match {
          case (
              DeclStmt(v @ VarDecl(name, _, None)),
              ExprStmt(Assignment(DeclRef(assigned), rhs))
            ) if name == assigned && !collectDeclRefs(rhs).contains(name) =>
            out += DeclStmt(withInit(v, Some(rhs)))
            i += 2
          case _ =>
            out += stmts(i)
            i += 1
        }
      } else {
        out += stmts(i)
        i += 1
      }
    }
    out.toSeq
  }

  private def singleAssignmentWithPureDecls(stmt: Stmt): Option[(Expr, Expr)] =
    stmt match {
      case ExprStmt(Assignment(lhs, rhs)) =>
        Some(lhs -> rhs)
      case Block(body) =>
        assignmentWithPureDecls(body)
      case _ =>
        None
    }

  private def assignmentWithPureDecls(stmts: Seq[Stmt]): Option[(Expr, Expr)] = {
    val decls = scala.collection.mutable.ArrayBuffer.empty[(String, Expr)]
    var assignment: Option[(Expr, Expr)] = None
    stmts.foreach {
      case DeclStmt(VarDecl(name, _: C.AST.BasicType, Some(init)))
          if pure(init) && assignment.isEmpty =>
        decls += name -> substituteDeclRefsExpr(init, decls.toSeq)
      case ExprStmt(Assignment(lhs, rhs)) =>
        if (assignment.nonEmpty) {
          return None
        }
        assignment = Some(
          substituteDeclRefsExpr(lhs, decls.toSeq) ->
            substituteDeclRefsExpr(rhs, decls.toSeq)
        )
      case Comment(_) =>
      case _ =>
        return None
    }
    assignment
  }

  private def substituteDeclRefsExpr(expr: Expr, replacements: Seq[(String, Expr)]): Expr =
    replacements.foldLeft(expr) { case (current, (name, replacement)) =>
      Nodes.VisitAndRebuild(current, new Nodes.VisitAndRebuild.Visitor {
        override def pre(n: Node): Result =
          n match {
            case DeclRef(`name`) =>
              Stop(replacement)
            case _ =>
              Continue(n, this)
        }
      })
    }

  private def substituteDeclRefsStmt(stmt: Stmt, replacements: Seq[(String, Expr)]): Stmt =
    stmt match {
      case Block(body) =>
        Block(body.map(substituteDeclRefsStmt(_, replacements)))
      case Stmts(a, b) =>
        Stmts(substituteDeclRefsStmt(a, replacements), substituteDeclRefsStmt(b, replacements))
      case DeclStmt(v @ VarDecl(_, _, init)) =>
        DeclStmt(withInit(v, init.map(substituteDeclRefsExpr(_, replacements))))
      case ExprStmt(Assignment(lhs, rhs)) =>
        ExprStmt(Assignment(
          substituteDeclRefsExpr(lhs, replacements),
          substituteDeclRefsExpr(rhs, replacements)
        ))
      case ExprStmt(expr) =>
        ExprStmt(substituteDeclRefsExpr(expr, replacements))
      case ForLoop(init, cond, increment, body) =>
        ForLoop(
          substituteDeclRefsStmt(init, replacements).asInstanceOf[DeclStmt],
          substituteDeclRefsExpr(cond, replacements),
          substituteDeclRefsExpr(increment, replacements),
          substituteDeclRefsStmt(body, replacements).asInstanceOf[Block]
        )
      case WhileLoop(cond, body) =>
        WhileLoop(substituteDeclRefsExpr(cond, replacements),
          substituteDeclRefsStmt(body, replacements))
      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(
          substituteDeclRefsExpr(cond, replacements),
          substituteDeclRefsStmt(trueBody, replacements),
          falseBody.map(substituteDeclRefsStmt(_, replacements))
        )
      case other =>
        other
    }

  private def inlineLiteralIntDecls(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        val rewritten = body.map(inlineLiteralIntDecls)
        val out = scala.collection.mutable.ArrayBuffer.empty[Stmt]
        val replacements = scala.collection.mutable.ArrayBuffer.empty[(String, Expr)]
        rewritten.zipWithIndex.foreach { case (s, i) =>
          s match {
            case DeclStmt(VarDecl(name, BasicType("int", _), Some(value)))
                if constInt(value).isDefined && !writesName(rewritten.drop(i + 1), name) =>
              replacements += name -> value
            case _ =>
              out += substituteDeclRefsStmt(s, replacements.toSeq)
          }
        }
        Block(out.toSeq)
      case Stmts(a, b) =>
        Stmts(inlineLiteralIntDecls(a), inlineLiteralIntDecls(b))
      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
          inlineLiteralIntDecls(body).asInstanceOf[Block])
      case WhileLoop(cond, body) =>
        WhileLoop(cond, inlineLiteralIntDecls(body))
      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, inlineLiteralIntDecls(trueBody), falseBody.map(inlineLiteralIntDecls))
      case other =>
        other
    }

  private def countDeclRefs(stmt: Stmt, name: String): Int = {
    var count = 0
    Nodes.VisitAndRebuild(stmt, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result =
        n match {
          case DeclRef(`name`) =>
            count += 1
            Continue(n, this)
          case _ =>
            Continue(n, this)
        }
    })
    count
  }

  private def simplifyExpressions(stmt: Stmt): Stmt =
    Nodes.VisitAndRebuild(stmt, new Nodes.VisitAndRebuild.Visitor {
      override def post(n: Node): Node =
        n match {
          case expr: Expr => simplifyExpr(expr)
          case other => other
        }
    })

  private def simplifyExpr(expr: Expr): Expr =
    expr match {
      case BinaryExpr(lhs, op, rhs) =>
        simplifyBinary(lhs, op, rhs)
      case TernaryExpr(cond, thenE, elseE) if isOne(cond) =>
        thenE
      case TernaryExpr(cond, thenE, elseE) if isZero(cond) =>
        elseE
      case TernaryExpr(
            cond,
            BinaryExpr(commonThen, BinaryOperator.+, thenTail),
            BinaryExpr(commonElse, BinaryOperator.+, elseTail))
          if sameExpr(commonThen, commonElse) && pure(commonThen) =>
        BinaryExpr(commonThen, BinaryOperator.+,
          TernaryExpr(cond, thenTail, elseTail))
      case UnaryExpr(UnaryOperator.!, BinaryExpr(lhs, BinaryOperator.<, rhs)) =>
        BinaryExpr(lhs, BinaryOperator.>=, rhs)
      case UnaryExpr(UnaryOperator.!, BinaryExpr(lhs, BinaryOperator.>, rhs)) =>
        BinaryExpr(lhs, BinaryOperator.<=, rhs)
      case UnaryExpr(UnaryOperator.!, BinaryExpr(lhs, BinaryOperator.<=, rhs)) =>
        BinaryExpr(lhs, BinaryOperator.>, rhs)
      case UnaryExpr(UnaryOperator.!, BinaryExpr(lhs, BinaryOperator.>=, rhs)) =>
        BinaryExpr(lhs, BinaryOperator.<, rhs)
      case UnaryExpr(UnaryOperator.!, BinaryExpr(lhs, BinaryOperator.==, rhs)) =>
        BinaryExpr(lhs, BinaryOperator.!=, rhs)
      case UnaryExpr(UnaryOperator.!, BinaryExpr(lhs, BinaryOperator.!=, rhs)) =>
        BinaryExpr(lhs, BinaryOperator.==, rhs)
      case UnaryExpr(UnaryOperator.!, UnaryExpr(UnaryOperator.!, inner)) =>
        inner
      case other =>
        other
    }

  private def factorRepeatedIntegerExprs(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        val recursivelyCleaned = body.map(factorRepeatedIntegerExprs)
        val usedNames = scala.collection.mutable.Set.empty[String]
        recursivelyCleaned.foreach(collectDeclNames(_, usedNames))
        val statementFactored = recursivelyCleaned.flatMap(factorStatement(_, usedNames))
        Block(factorPureIntegerDeclRuns(statementFactored, usedNames))

      case Stmts(a, b) =>
        blockOrStmt(flatten(Stmts(
          factorRepeatedIntegerExprs(a),
          factorRepeatedIntegerExprs(b)
        )))

      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
          factorRepeatedIntegerExprs(body).asInstanceOf[Block])

      case WhileLoop(cond, body) =>
        WhileLoop(cond, factorRepeatedIntegerExprs(body))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, factorRepeatedIntegerExprs(trueBody),
          falseBody.map(factorRepeatedIntegerExprs))

      case other =>
        other
    }

  private def inlineSingleUseScalarDecls(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        Block(inlineSingleUseDeclRuns(body.map(inlineSingleUseScalarDecls)))

      case Stmts(a, b) =>
        blockOrStmt(inlineSingleUseDeclRuns(flatten(Stmts(
          inlineSingleUseScalarDecls(a),
          inlineSingleUseScalarDecls(b)
        ))))

      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
          inlineSingleUseScalarDecls(body).asInstanceOf[Block])

      case WhileLoop(cond, body) =>
        WhileLoop(cond, inlineSingleUseScalarDecls(body))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, inlineSingleUseScalarDecls(trueBody),
          falseBody.map(inlineSingleUseScalarDecls))

      case other =>
        other
    }

  private type QuerySeen = Map[(String, String), String]

  private def reuseIdenticalOpenCLQueryDecls(stmt: Stmt): Stmt =
    reuseIdenticalOpenCLQueryDecls(stmt, Map.empty, Seq.empty)

  private def reuseIdenticalOpenCLQueryDecls(
      stmt: Stmt,
      inheritedSeen: QuerySeen,
      inheritedReplacements: Seq[(String, Expr)]
    ): Stmt =
    stmt match {
      case Block(body) =>
        Block(reuseIdenticalOpenCLQueryDeclsInBlock(
          body,
          inheritedSeen,
          inheritedReplacements
        ))

      case Stmts(a, b) =>
        blockOrStmt(reuseIdenticalOpenCLQueryDeclsInBlock(flatten(Stmts(
          substituteDeclRefsStmt(a, inheritedReplacements),
          substituteDeclRefsStmt(b, inheritedReplacements)
        )), inheritedSeen, inheritedReplacements))

      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
          reuseIdenticalOpenCLQueryDecls(
            body,
            inheritedSeen,
            inheritedReplacements
          ).asInstanceOf[Block])

      case WhileLoop(cond, body) =>
        WhileLoop(cond, reuseIdenticalOpenCLQueryDecls(
          body,
          inheritedSeen,
          inheritedReplacements
        ))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, reuseIdenticalOpenCLQueryDecls(
          trueBody,
          inheritedSeen,
          inheritedReplacements
        ), falseBody.map(reuseIdenticalOpenCLQueryDecls(
          _,
          inheritedSeen,
          inheritedReplacements
        )))

      case other =>
        substituteDeclRefsStmt(other, inheritedReplacements)
    }

  private def reuseIdenticalOpenCLQueryDeclsInBlock(
      stmts: Seq[Stmt],
      inheritedSeen: QuerySeen,
      inheritedReplacements: Seq[(String, Expr)]
    ): Seq[Stmt] = {
    val out = scala.collection.mutable.ArrayBuffer.empty[Stmt]
    val seen = scala.collection.mutable.Map.empty[(String, String), String] ++ inheritedSeen
    var replacements = inheritedReplacements

    stmts.foreach {
      case DeclStmt(VarDecl(name, t @ BasicType(_, _), Some(init))) =>
        val rewrittenInit = substituteDeclRefsExpr(init, replacements)
        openCLQueryExprKey(rewrittenInit) match {
          case Some(key) =>
            val typedKey = t.toString -> key
            seen.get(typedKey) match {
              case Some(existing) =>
                replacements :+= name -> DeclRef(existing)
              case None =>
                seen(typedKey) = name
                out += DeclStmt(VarDecl(name, t, Some(rewrittenInit)))
            }
          case None =>
            out += DeclStmt(VarDecl(name, t, Some(rewrittenInit)))
        }

      case other =>
        out += reuseIdenticalOpenCLQueryDecls(
          other,
          seen.toMap,
          replacements
        )
    }

    out.toSeq
  }

  private type KnownIntegerExprs = Map[String, String]

  private def reuseKnownIntegerSubexpressions(stmt: Stmt): Stmt =
    reuseKnownIntegerSubexpressions(stmt, Map.empty)

  private def reuseKnownIntegerSubexpressions(
      stmt: Stmt,
      inheritedSeen: KnownIntegerExprs
    ): Stmt =
    stmt match {
      case Block(body) =>
        val out = scala.collection.mutable.ArrayBuffer.empty[Stmt]
        val seen = scala.collection.mutable.Map.empty[String, String] ++ inheritedSeen
        body.foreach { s =>
          val rewritten = reuseKnownIntegerSubexpressions(s, seen.toMap)
          out += rewritten
          rewritten match {
            case DeclStmt(VarDecl(name, BasicType("int", _), Some(init)))
                if reusableKnownIntegerExpr(init) =>
              seen.getOrElseUpdate(C.AST.Printer(init), name)
            case _ =>
          }
        }
        Block(out.toSeq)

      case Stmts(a, b) =>
        blockOrStmt(flatten(Stmts(
          reuseKnownIntegerSubexpressions(a, inheritedSeen),
          reuseKnownIntegerSubexpressions(b, inheritedSeen)
        )))

      case ForLoop(init, cond, increment, body) =>
        ForLoop(
          rewriteKnownIntegerSubexpressions(init, inheritedSeen).asInstanceOf[DeclStmt],
          rewriteKnownIntegerSubexpressionsExpr(cond, inheritedSeen),
          rewriteKnownIntegerSubexpressionsExpr(increment, inheritedSeen),
          reuseKnownIntegerSubexpressions(body, inheritedSeen).asInstanceOf[Block]
        )

      case WhileLoop(cond, body) =>
        WhileLoop(
          rewriteKnownIntegerSubexpressionsExpr(cond, inheritedSeen),
          reuseKnownIntegerSubexpressions(body, inheritedSeen)
        )

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(
          rewriteKnownIntegerSubexpressionsExpr(cond, inheritedSeen),
          reuseKnownIntegerSubexpressions(trueBody, inheritedSeen),
          falseBody.map(reuseKnownIntegerSubexpressions(_, inheritedSeen))
        )

      case other =>
        rewriteKnownIntegerSubexpressions(other, inheritedSeen)
    }

  private def rewriteKnownIntegerSubexpressions(
      stmt: Stmt,
      seen: KnownIntegerExprs
    ): Stmt =
    stmt match {
      case DeclStmt(v @ VarDecl(_, _, init)) =>
        DeclStmt(withInit(v, init.map(rewriteKnownIntegerSubexpressionsExpr(_, seen))))
      case ExprStmt(Assignment(lhs, rhs)) =>
        ExprStmt(Assignment(
          rewriteKnownIntegerSubexpressionsExpr(lhs, seen),
          rewriteKnownIntegerSubexpressionsExpr(rhs, seen)
        ))
      case ExprStmt(expr) =>
        ExprStmt(rewriteKnownIntegerSubexpressionsExpr(expr, seen))
      case other =>
        other
    }

  private def rewriteKnownIntegerSubexpressionsExpr(
      expr: Expr,
      seen: KnownIntegerExprs
    ): Expr = {
    def replaceWhole(e: Expr): Option[Expr] =
      if (reusableKnownIntegerExpr(e)) {
        seen.get(C.AST.Printer(e)).map(name => DeclRef(name))
      } else {
        None
      }

    replaceWhole(expr).getOrElse {
      expr match {
        case BinaryExpr(lhs, op, rhs) =>
          val rewritten = BinaryExpr(
            rewriteKnownIntegerSubexpressionsExpr(lhs, seen),
            op,
            rewriteKnownIntegerSubexpressionsExpr(rhs, seen)
          )
          replaceWhole(rewritten).getOrElse(rewritten)
        case UnaryExpr(op, e) =>
          val rewritten = UnaryExpr(op, rewriteKnownIntegerSubexpressionsExpr(e, seen))
          replaceWhole(rewritten).getOrElse(rewritten)
        case TernaryExpr(cond, thenE, elseE) =>
          val rewritten = TernaryExpr(
            rewriteKnownIntegerSubexpressionsExpr(cond, seen),
            rewriteKnownIntegerSubexpressionsExpr(thenE, seen),
            rewriteKnownIntegerSubexpressionsExpr(elseE, seen)
          )
          replaceWhole(rewritten).getOrElse(rewritten)
        case ArraySubscript(array, index) =>
          ArraySubscript(array, rewriteKnownIntegerSubexpressionsExpr(index, seen))
        case Cast(t, e) =>
          val rewritten = Cast(t, rewriteKnownIntegerSubexpressionsExpr(e, seen))
          replaceWhole(rewritten).getOrElse(rewritten)
        case other =>
          other
      }
    }
  }

  private def openCLQueryExprKey(expr: Expr): Option[String] =
    expr match {
      case FunCall(DeclRef(name), args) if pureOpenCLQuery(name) && args.forall(pure) =>
        Some(FunCall(DeclRef(name), args).toString)
      case ArithmeticExpr(ae) if openCLQueryText(ae.toString).nonEmpty =>
        Some(ae.toString)
      case Literal(text) if openCLQueryText(text).nonEmpty =>
        Some(text)
      case _ =>
        None
    }

  private def openCLQueryText(text: String): Option[String] = {
    val name = text.takeWhile(_ != '(')
    if (pureOpenCLQuery(name)) Some(text) else None
  }

  private def inlineSingleUseDeclRuns(stmts: Seq[Stmt]): Seq[Stmt] = {
    val out = scala.collection.mutable.ArrayBuffer.empty[Stmt]
    var i = 0
    while (i < stmts.length) {
      val run = scala.collection.mutable.ArrayBuffer.empty[DeclStmt]
      var j = i
      while (j < stmts.length && pureScalarDecl(stmts(j)).isDefined) {
        run += stmts(j).asInstanceOf[DeclStmt]
        j += 1
      }

      if (run.nonEmpty && j < stmts.length && inlineConsumer(stmts(j))) {
        val rest = stmts.drop(j + 1)
        val (keptDecls, rewrittenConsumer) =
          inlineRunIntoConsumer(run.toSeq, stmts(j), rest)
        out ++= keptDecls
        out += rewrittenConsumer
        i = j + 1
      } else {
        out += stmts(i)
        i += 1
      }
    }
    out.toSeq
  }

  private def inlineRunIntoConsumer(
      decls: Seq[DeclStmt],
      consumer: Stmt,
      rest: Seq[Stmt]
    ): (Seq[Stmt], Stmt) = {
    var currentDecls = decls
    var currentConsumer = consumer
    var changed = true

    while (changed) {
      changed = false

      currentDecls.zipWithIndex.collectFirst {
        case (d @ DeclStmt(VarDecl(name, t, Some(init))), index)
            if pure(init) &&
              inlineableScalarDeclUse(
                t,
                init,
                (currentDecls.drop(index + 1) :+ currentConsumer).map(countDeclRefs(_, name)).sum
              ) &&
              rest.map(countDeclRefs(_, name)).sum == 0 =>
          d -> (name -> init)
      }.foreach { case (decl, replacement) =>
        currentDecls = currentDecls.filterNot(_ == decl).map {
          case DeclStmt(VarDecl(n, dt, di)) =>
            DeclStmt(VarDecl(n, dt, di.map(substituteDeclRefsExpr(_, Seq(replacement)))))
        }
        currentConsumer = substituteDeclRefsStmt(currentConsumer, Seq(replacement))
        changed = true
      }
    }

    currentDecls -> currentConsumer
  }

  private def inlineableScalarDeclUse(t: Type, init: Expr, uses: Int): Boolean =
    uses == 1 || (uses <= 2 && smallIntegerExpr(t, init))

  private def smallIntegerExpr(t: Type, expr: Expr): Boolean =
    t match {
      case BasicType("int", _) => exprSize(expr) <= 3 && localIntegerExpr(expr)
      case _ => false
    }

  private def localIntegerExpr(expr: Expr): Boolean =
    expr match {
      case _: Literal | _: DeclRef | _: ArithmeticExpr => true
      case UnaryExpr(_, e) => localIntegerExpr(e)
      case BinaryExpr(lhs, op, rhs) if integerOperator(op) =>
        localIntegerExpr(lhs) && localIntegerExpr(rhs)
      case _ => false
    }

  private def pureScalarDecl(stmt: Stmt): Option[(String, Expr)] =
    stmt match {
      case DeclStmt(VarDecl(name, _: C.AST.BasicType, Some(init))) if pure(init) =>
        Some(name -> init)
      case _ =>
        None
    }

  private def inlineConsumer(stmt: Stmt): Boolean =
    stmt match {
      case DeclStmt(_) | ExprStmt(_) => true
      case _ => false
    }

  private def factorStatement(
      stmt: Stmt,
      usedNames: scala.collection.mutable.Set[String]
    ): Seq[Stmt] =
    stmt match {
      case DeclStmt(VarDecl(name, t @ BasicType("int", _), Some(init))) =>
        val (temps, rewrittenInit) = factorExprIntoIntegerTemps(init, usedNames)
        temps :+ DeclStmt(VarDecl(name, t, Some(rewrittenInit)))
      case ExprStmt(Assignment(lhs, rhs)) =>
        val (temps, rewrittenRhs) = factorExprIntoIntegerTemps(rhs, usedNames)
        temps :+ ExprStmt(Assignment(lhs, rewrittenRhs))
      case _ =>
        Seq(stmt)
    }

  private def factorPureIntegerDeclRuns(
      stmts: Seq[Stmt],
      usedNames: scala.collection.mutable.Set[String]
    ): Seq[Stmt] = {
    val out = scala.collection.mutable.ArrayBuffer.empty[Stmt]
    var i = 0
    while (i < stmts.length) {
      val run = scala.collection.mutable.ArrayBuffer.empty[DeclStmt]
      var j = i
      while (j < stmts.length) {
        stmts(j) match {
          case d @ DeclStmt(VarDecl(_, BasicType("int", _), Some(init)))
              if pure(init) =>
            run += d
            j += 1
          case _ =>
            j = stmts.length
        }
      }

      if (run.length >= 3) {
        val rewritten = factorIntegerDeclRun(run.toSeq, usedNames)
        out ++= rewritten
        i += run.length
      } else {
        out += stmts(i)
        i += 1
      }
    }
    out.toSeq
  }

  private def factorIntegerDeclRun(
      decls: Seq[DeclStmt],
      usedNames: scala.collection.mutable.Set[String]
    ): Seq[Stmt] = {
    val declaredInRun = decls.collect {
      case DeclStmt(VarDecl(name, _, _)) => name
    }.toSet

    val inits = decls.collect {
      case DeclStmt(VarDecl(_, _, Some(init))) => init
    }
    chooseRepeatedIntegerExpr(inits, disallowedRefs = declaredInRun) match {
      case Some(candidate) =>
        val tmp = freshName("_np_cse", usedNames)
        DeclStmt(VarDecl(tmp, Type.int, Some(candidate))) +:
          decls.map {
            case DeclStmt(VarDecl(name, t, Some(init))) =>
              DeclStmt(VarDecl(name, t, Some(replaceExpr(init, candidate, DeclRef(tmp)))))
            case other =>
              other
          }
      case None =>
        decls
    }
  }

  private def reuseIdenticalPureValueAssignments(stmt: Stmt): Stmt =
    stmt match {
      case Block(body) =>
        Block(reuseIdenticalPureValueAssignmentsInBlock(
          body.map(reuseIdenticalPureValueAssignments)))

      case Stmts(a, b) =>
        blockOrStmt(reuseIdenticalPureValueAssignmentsInBlock(flatten(Stmts(
          reuseIdenticalPureValueAssignments(a),
          reuseIdenticalPureValueAssignments(b)
        ))))

      case ForLoop(init, cond, increment, body) =>
        ForLoop(init.asInstanceOf[DeclStmt], cond, increment,
          reuseIdenticalPureValueAssignments(body).asInstanceOf[Block])

      case WhileLoop(cond, body) =>
        WhileLoop(cond, reuseIdenticalPureValueAssignments(body))

      case IfThenElse(cond, trueBody, falseBody) =>
        IfThenElse(cond, reuseIdenticalPureValueAssignments(trueBody),
          falseBody.map(reuseIdenticalPureValueAssignments))

      case other =>
        other
    }

  private def reuseIdenticalPureValueAssignmentsInBlock(stmts: Seq[Stmt]): Seq[Stmt] = {
    val out = scala.collection.mutable.ArrayBuffer.empty[Stmt]
    val declTypes = scala.collection.mutable.Map.empty[String, Type]
    val seen = scala.collection.mutable.Map.empty[(String, String), String]

    def forgetWritten(stmt: Stmt): Unit =
      assignedNames(stmt).foreach { name =>
        seen.filterInPlace { case (_, existing) => existing != name }
      }

    stmts.foreach {
      case d @ DeclStmt(VarDecl(name, t, _)) =>
        declTypes(name) = t
        out += d

      case s @ ExprStmt(Assignment(DeclRef(name), rhs)) =>
        forgetWritten(s)
        declTypes.get(name) match {
          case Some(t) if reusableValueType(t) && pure(rhs) && !collectDeclRefs(rhs).contains(name) =>
            val key = (typeKey(t), shine.OpenCL.AST.Printer(rhs))
            seen.get(key) match {
              case Some(existing) if existing != name =>
                out += ExprStmt(Assignment(DeclRef(name), DeclRef(existing)))
              case _ =>
                seen(key) = name
                out += s
            }
          case _ =>
            out += s
        }

      case other =>
        forgetWritten(other)
        out += other
    }

    out.toSeq
  }

  private def reusableValueType(t: Type): Boolean =
    t match {
      case BasicType(name, _) =>
        name == "float" || name.startsWith("float") ||
          name == "double" || name.startsWith("double")
      case OpaqueType(name) =>
        name == "float" || name.startsWith("float") ||
          name == "double" || name.startsWith("double")
      case _ => false
    }

  private def typeKey(t: Type): String =
    t.toString

  private def factorExprIntoIntegerTemps(
      expr: Expr,
      usedNames: scala.collection.mutable.Set[String]
    ): (Seq[Stmt], Expr) = {
    val temps = scala.collection.mutable.ArrayBuffer.empty[Stmt]
    var current = expr
    var remaining = MaxIntegerCseTempsPerStatement
    while (remaining > 0) {
      chooseRepeatedIntegerExpr(current) match {
        case Some(candidate) =>
          val tmp = freshName("_np_cse", usedNames)
          temps += DeclStmt(VarDecl(tmp, Type.int, Some(candidate)))
          current = replaceExpr(current, candidate, DeclRef(tmp))
          remaining -= 1
        case None =>
          remaining = 0
      }
    }
    temps.toSeq -> current
  }

  private def chooseRepeatedIntegerExpr(expr: Expr): Option[Expr] = {
    chooseRepeatedIntegerExpr(Seq(expr), disallowedRefs = Set.empty)
  }

  private def chooseRepeatedIntegerExpr(
      exprs: Seq[Expr],
      disallowedRefs: Set[String]
    ): Option[Expr] = {
    val counts = scala.collection.mutable.Map.empty[String, (Expr, Int)]
    exprs.flatMap(collectIntegerSubexprs).foreach { e =>
      val key = C.AST.Printer(e)
      val (_, count) = counts.getOrElse(key, e -> 0)
      counts.update(key, e -> (count + 1))
    }
    val eligible = counts.values.collect {
      case (e, count) if collectDeclRefs(e).intersect(disallowedRefs).isEmpty =>
        (e, count)
    }.toSeq

    val ordinary = eligible.collect {
      case (e, count) if ordinaryCseCandidate(e, count) =>
        (e, ordinaryCseScore(e, count))
    }.sortBy { case (e, score) => (-score, -exprSize(e), e.toString) }
      .headOption.map(_._1)

    ordinary.orElse {
      eligible.collect {
        case (e, count) if repeatedExpensiveIntegerOpCandidate(e, count) =>
          (e, expensiveIntegerOpCseScore(e, count))
      }.sortBy { case (e, score) => (-score, -exprSize(e), e.toString) }
        .headOption.map(_._1)
    }
  }

  private def ordinaryCseCandidate(expr: Expr, count: Int): Boolean = {
    val size = exprSize(expr)
    count >= 3 && size >= 4 && ((count - 1) * size) >= 15
  }

  private def ordinaryCseScore(expr: Expr, count: Int): Int =
    (count - 1) * exprSize(expr)

  private def repeatedExpensiveIntegerOpCandidate(expr: Expr, count: Int): Boolean = {
    val size = exprSize(expr)
    count >= 2 && (containsIntegerDivOrMod(expr) || containsShiftOrMask(expr)) && size >= 3
  }

  private def expensiveIntegerOpCseScore(expr: Expr, count: Int): Int = {
    val size = exprSize(expr)
    ((count - 1) * size) + count
  }

  private def collectIntegerSubexprs(expr: Expr): Seq[Expr] = {
    val children = expr match {
      case BinaryExpr(lhs, _, rhs) =>
        collectIntegerSubexprs(lhs) ++ collectIntegerSubexprs(rhs)
      case UnaryExpr(_, e) =>
        collectIntegerSubexprs(e)
      case TernaryExpr(cond, thenE, elseE) =>
        collectIntegerSubexprs(cond) ++ collectIntegerSubexprs(thenE) ++
          collectIntegerSubexprs(elseE)
      case ArraySubscript(_, index) =>
        collectIntegerSubexprs(index)
      case Cast(_, e) =>
        collectIntegerSubexprs(e)
      case _ =>
        Seq.empty
    }
    if (integerPure(expr) && !atomic(expr)) expr +: children else children
  }

  private def replaceExpr(expr: Expr, target: Expr, replacement: Expr): Expr =
    if (sameExpr(expr, target)) {
      replacement
    } else {
      expr match {
        case BinaryExpr(lhs, op, rhs) =>
          BinaryExpr(replaceExpr(lhs, target, replacement), op,
            replaceExpr(rhs, target, replacement))
        case UnaryExpr(op, e) =>
          UnaryExpr(op, replaceExpr(e, target, replacement))
        case TernaryExpr(cond, thenE, elseE) =>
          TernaryExpr(
            replaceExpr(cond, target, replacement),
            replaceExpr(thenE, target, replacement),
            replaceExpr(elseE, target, replacement)
          )
        case ArraySubscript(array, index) =>
          ArraySubscript(array, replaceExpr(index, target, replacement))
        case Cast(t, e) =>
          Cast(t, replaceExpr(e, target, replacement))
        case other =>
          other
      }
    }

  private def exprSize(expr: Expr): Int =
    expr match {
      case BinaryExpr(lhs, _, rhs) => 1 + exprSize(lhs) + exprSize(rhs)
      case UnaryExpr(_, e) => 1 + exprSize(e)
      case TernaryExpr(cond, thenE, elseE) =>
        1 + exprSize(cond) + exprSize(thenE) + exprSize(elseE)
      case ArraySubscript(_, index) => 1 + exprSize(index)
      case Cast(_, e) => 1 + exprSize(e)
      case _ => 1
    }

  private def containsIntegerDivOrMod(expr: Expr): Boolean =
    expr match {
      case BinaryExpr(_, BinaryOperator./, _) | BinaryExpr(_, BinaryOperator.%, _) =>
        true
      case BinaryExpr(lhs, _, rhs) =>
        containsIntegerDivOrMod(lhs) || containsIntegerDivOrMod(rhs)
      case UnaryExpr(_, e) =>
        containsIntegerDivOrMod(e)
      case TernaryExpr(cond, thenE, elseE) =>
        containsIntegerDivOrMod(cond) || containsIntegerDivOrMod(thenE) ||
          containsIntegerDivOrMod(elseE)
      case ArraySubscript(_, index) =>
        containsIntegerDivOrMod(index)
      case Cast(_, e) =>
        containsIntegerDivOrMod(e)
      case _ =>
        false
    }

  private def containsShiftOrMask(expr: Expr): Boolean =
    expr match {
      case BinaryExpr(_, BinaryOperator.>>, _) | BinaryExpr(_, BinaryOperator.bitAnd, _) =>
        true
      case BinaryExpr(lhs, _, rhs) =>
        containsShiftOrMask(lhs) || containsShiftOrMask(rhs)
      case UnaryExpr(_, e) =>
        containsShiftOrMask(e)
      case TernaryExpr(cond, thenE, elseE) =>
        containsShiftOrMask(cond) || containsShiftOrMask(thenE) ||
          containsShiftOrMask(elseE)
      case ArraySubscript(_, index) =>
        containsShiftOrMask(index)
      case Cast(_, e) =>
        containsShiftOrMask(e)
      case _ =>
        false
    }

  private def integerPure(expr: Expr): Boolean =
    expr match {
      case _: Literal | _: DeclRef | _: ArithmeticExpr => true
      case UnaryExpr(UnaryOperator.!, e) => integerPure(e)
      case UnaryExpr(UnaryOperator.-, e) => integerPure(e)
      case BinaryExpr(lhs, op, rhs) if integerOperator(op) =>
        integerPure(lhs) && integerPure(rhs)
      case TernaryExpr(cond, thenE, elseE) =>
        integerPure(cond) && integerPure(thenE) && integerPure(elseE)
      case Cast(BasicType("int", _), e) =>
        integerPure(e)
      case _ =>
        false
    }

  private def integerOperator(op: BinaryOperator.Value): Boolean =
    op == BinaryOperator.+ || op == BinaryOperator.- ||
      op == BinaryOperator.* || op == BinaryOperator./ ||
      op == BinaryOperator.% || op == BinaryOperator.< ||
      op == BinaryOperator.> || op == BinaryOperator.<= ||
      op == BinaryOperator.>= || op == BinaryOperator.== ||
      op == BinaryOperator.!= || op == BinaryOperator.&& ||
      op == BinaryOperator.|| || op == BinaryOperator.^ ||
      op == BinaryOperator.<< || op == BinaryOperator.>> ||
      op == BinaryOperator.bitAnd

  private def atomic(expr: Expr): Boolean =
    expr match {
      case _: Literal | _: DeclRef | _: ArithmeticExpr => true
      case _ => false
    }

  private def collectDeclNames(
      stmt: Stmt,
      names: scala.collection.mutable.Set[String]
    ): Unit =
    stmt match {
      case Block(body) =>
        body.foreach(collectDeclNames(_, names))
      case Stmts(a, b) =>
        collectDeclNames(a, names)
        collectDeclNames(b, names)
      case ForLoop(init, _, _, body) =>
        collectDeclNames(init, names)
        collectDeclNames(body, names)
      case WhileLoop(_, body) =>
        collectDeclNames(body, names)
      case IfThenElse(_, trueBody, falseBody) =>
        collectDeclNames(trueBody, names)
        falseBody.foreach(collectDeclNames(_, names))
      case DeclStmt(VarDecl(name, _, _)) =>
        names += name
      case _ =>
    }

  private def collectDeclRefs(expr: Expr): Set[String] = {
    val refs = scala.collection.mutable.Set.empty[String]
    Nodes.VisitAndRebuild(expr, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result =
        n match {
          case DeclRef(name) =>
            refs += name
            Continue(n, this)
          case _ =>
            Continue(n, this)
        }
    })
    refs.toSet
  }

  private def freshName(
      prefix: String,
      usedNames: scala.collection.mutable.Set[String]
    ): String = {
    var i = 0
    var name = s"${prefix}${i}"
    while (usedNames.contains(name)) {
      i += 1
      name = s"${prefix}${i}"
    }
    usedNames += name
    name
  }

  private def simplifyBinary(lhs: Expr, op: BinaryOperator.Value, rhs: Expr): Expr =
    op match {
      case BinaryOperator.% =>
        simplifyModulo(lhs, rhs)
      case _ if constInt(lhs).isDefined && constInt(rhs).isDefined =>
        foldIntBinary(constInt(lhs).get, op, constInt(rhs).get)
          .map(v => Literal(v.toString))
          .getOrElse(BinaryExpr(lhs, op, rhs))
      case BinaryOperator.+ if isZero(lhs) => rhs
      case BinaryOperator.+ if isZero(rhs) => lhs
      case BinaryOperator.- if isZero(rhs) => lhs
      case BinaryOperator.* if isOne(lhs) => rhs
      case BinaryOperator.* if isOne(rhs) => lhs
      case BinaryOperator.* if isZero(lhs) => lhs
      case BinaryOperator.* if isZero(rhs) => rhs
      case BinaryOperator./ if isOne(rhs) => lhs
      case BinaryOperator.&& if isZero(lhs) || isZero(rhs) => Literal("0")
      case BinaryOperator.&& if isOne(lhs) => rhs
      case BinaryOperator.&& if isOne(rhs) => lhs
      case BinaryOperator.|| if isOne(lhs) || isOne(rhs) => Literal("1")
      case BinaryOperator.|| if isZero(lhs) => rhs
      case BinaryOperator.|| if isZero(rhs) => lhs
      case _ => BinaryExpr(lhs, op, rhs)
    }

  private def simplifyModulo(lhs: Expr, rhs: Expr): Expr =
    lhs match {
      case _ if constInt(lhs).isDefined && constInt(rhs).exists(_ != 0) =>
        Literal((constInt(lhs).get % constInt(rhs).get).toString)
      case BinaryExpr(inner, BinaryOperator.%, innerMod)
          if constInt(innerMod).exists(m => constInt(rhs).exists(n => n != 0 && m % n == 0)) =>
        BinaryExpr(inner, BinaryOperator.%, rhs)
      case _ if isOne(rhs) =>
        Literal("0")
      case _ =>
        BinaryExpr(lhs, BinaryOperator.%, rhs)
    }

  private def foldIntBinary(lhs: Int, op: BinaryOperator.Value, rhs: Int): Option[Int] =
    op match {
      case BinaryOperator.+ => Some(lhs + rhs)
      case BinaryOperator.- => Some(lhs - rhs)
      case BinaryOperator.* => Some(lhs * rhs)
      case BinaryOperator./ if rhs != 0 => Some(lhs / rhs)
      case BinaryOperator.>> if rhs >= 0 => Some(lhs >> rhs)
      case BinaryOperator.bitAnd => Some(lhs & rhs)
      case BinaryOperator.== => Some(if (lhs == rhs) 1 else 0)
      case BinaryOperator.!= => Some(if (lhs != rhs) 1 else 0)
      case BinaryOperator.< => Some(if (lhs < rhs) 1 else 0)
      case BinaryOperator.<= => Some(if (lhs <= rhs) 1 else 0)
      case BinaryOperator.> => Some(if (lhs > rhs) 1 else 0)
      case BinaryOperator.>= => Some(if (lhs >= rhs) 1 else 0)
      case _ => None
    }

  private def isZero(expr: Expr): Boolean =
    expr match {
      case Literal("0") | Literal("0.0f") => true
      case ArithmeticExpr(Cst(0)) => true
      case Cast(_, e) => isZero(e)
      case shine.OpenCL.AST.VectorLiteral(_, values) => values.forall(isZero)
      case _ => false
    }

  private def isOne(expr: Expr): Boolean =
    expr match {
      case Literal("1") | Literal("1.0f") => true
      case ArithmeticExpr(Cst(1)) => true
      case _ => false
    }

  private def sameExpr(a: Expr, b: Expr): Boolean =
    a == b || a.toString == b.toString

  private def constInt(expr: Expr): Option[Int] =
    expr match {
      case Literal(text) =>
        text.toIntOption
      case ArithmeticExpr(Cst(value)) =>
        Some(value.toInt)
      case _ =>
        None
    }

  private def removeUnusedScalarDecls(stmts: Seq[Stmt]): Seq[Stmt] = {
    stmts.zipWithIndex.flatMap { case (stmt, i) =>
      stmt match {
        case DeclStmt(VarDecl(name, _: C.AST.BasicType, init))
            if init.forall(pure) && !referencesName(stmts.drop(i + 1), name) =>
          None
        case _ =>
          Some(stmt)
      }
    }
  }

  private def referencesName(stmts: Seq[Stmt], name: String): Boolean =
    stmts.exists(referencesName(_, name))

  private def referencesName(stmt: Stmt, name: String): Boolean = {
    var found = false
    Nodes.VisitAndRebuild(stmt, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result =
        n match {
          case DeclRef(`name`) =>
            found = true
            Stop(n)
          case _ =>
            Continue(n, this)
        }
    })
    found
  }

  private def writesName(stmts: Seq[Stmt], name: String): Boolean =
    stmts.exists(writesName(_, name))

  private def writesName(stmt: Stmt, name: String): Boolean = {
    var found = false
    Nodes.VisitAndRebuild(stmt, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result =
        n match {
          case DeclStmt(OpenCL.AST.VarDecl(`name`, _, _, Some(_))) =>
            found = true
            Stop(n)
          case DeclStmt(VarDecl(`name`, _, Some(_))) =>
            found = true
            Stop(n)
          case Assignment(lhs, _) if lvalueRoot(lhs).contains(name) =>
            found = true
            Stop(n)
          case _ =>
            Continue(n, this)
        }
    })
    found
  }

  private def writeRootNames(stmt: Stmt): Set[String] = {
    val names = scala.collection.mutable.Set.empty[String]
    Nodes.VisitAndRebuild(stmt, new Nodes.VisitAndRebuild.Visitor {
      override def pre(n: Node): Result =
        n match {
          case DeclStmt(OpenCL.AST.VarDecl(name, _, _, Some(_))) =>
            names += name
            Continue(n, this)
          case DeclStmt(VarDecl(name, _, Some(_))) =>
            names += name
            Continue(n, this)
          case Assignment(lhs, _) =>
            lvalueRoot(lhs).foreach(names += _)
            Continue(n, this)
          case _ =>
            Continue(n, this)
        }
    })
    names.toSet
  }

  private def readsAny(stmt: Stmt, names: Set[String]): Boolean =
    names.nonEmpty && readNames(stmt).exists(names)

  private def readNames(stmt: Stmt): Set[String] = {
    val names = scala.collection.mutable.Set.empty[String]

    def expr(e: Expr): Unit =
      Nodes.VisitAndRebuild(e, new Nodes.VisitAndRebuild.Visitor {
        override def pre(n: Node): Result =
          n match {
            case DeclRef(name) =>
              names += name
              Continue(n, this)
            case _ =>
              Continue(n, this)
          }
      })

    def loop(s: Stmt): Unit =
      s match {
        case ExprStmt(Assignment(lhs, rhs)) =>
          expr(rhs)
          lhs match {
            case ArraySubscript(_, index) =>
              expr(index)
            case StructMemberAccess(_, _) =>
            case _ =>
          }
        case ExprStmt(e) =>
          expr(e)
        case DeclStmt(VarDecl(_, _, Some(init))) =>
          expr(init)
        case Block(body) =>
          body.foreach(loop)
        case Stmts(a, b) =>
          loop(a); loop(b)
        case ForLoop(init, cond, increment, body) =>
          loop(init); expr(cond); expr(increment); loop(body)
        case WhileLoop(cond, body) =>
          expr(cond); loop(body)
        case IfThenElse(cond, trueBody, falseBody) =>
          expr(cond); loop(trueBody); falseBody.foreach(loop)
        case _ =>
      }

    loop(stmt)
    names.toSet
  }

  private def lvalueRoot(expr: Expr): Option[String] =
    expr match {
      case DeclRef(name) => Some(name)
      case ArraySubscript(array, _) => lvalueRoot(array)
      case StructMemberAccess(struct, _) => lvalueRoot(struct)
      case _ => None
    }

  private def pure(expr: Expr): Boolean =
    expr match {
      case _: Literal | _: DeclRef | _: ArithmeticExpr => true
      case shine.OpenCL.AST.VectorLiteral(_, values) => values.forall(pure)
      case FunCall(DeclRef(name), _) if pureOpenCLQuery(name) => true
      case UnaryExpr(_, e) => pure(e)
      case BinaryExpr(lhs, _, rhs) => pure(lhs) && pure(rhs)
      case TernaryExpr(cond, thenE, elseE) => pure(cond) && pure(thenE) && pure(elseE)
      case Cast(_, e) => pure(e)
      case ArraySubscript(array, index) => pure(array) && pure(index)
      case StructMemberAccess(struct, _) => pure(struct)
      case _ => false
    }

  private def pureOpenCLQuery(name: String): Boolean =
    name match {
      case "get_global_id" | "get_local_id" | "get_group_id" |
           "get_global_size" | "get_local_size" | "get_num_groups" |
           "get_global_offset" | "get_work_dim" =>
        true
      case _ =>
        false
    }

  private def isComment(stmt: Stmt): Boolean =
    stmt match {
      case Comment(_) => true
      case _ => false
    }

  private def flatten(stmt: Stmt): Seq[Stmt] =
    stmt match {
      case Block(body) => body.flatMap(flatten)
      case Stmts(a, b) => flatten(a) ++ flatten(b)
      case Comment(_) => Seq.empty
      case other => Seq(other)
    }

  private def blockOrStmt(stmts: Seq[Stmt]): Stmt =
    stmts match {
      case Seq(single) => single
      case many => Block(many)
    }
}
