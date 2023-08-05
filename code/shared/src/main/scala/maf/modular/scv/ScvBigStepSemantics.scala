package maf.modular.scv

import maf.language.scheme.*
import maf.language.ContractScheme.ContractValues.*
import maf.language.symbolic.*
import maf.language.ContractScheme.*
import maf.language.sexp.Value
import maf.modular.ModAnalysis
import maf.modular.scheme.SchemeDomain
import maf.modular.scheme.modflocal.SchemeModFLocalSensitivity
import maf.modular.scheme.modflocal.SchemeSemantics
import maf.util.benchmarks.Timeout
import maf.util.{MonoidInstances, TaggedSet}
import maf.core.{Identifier, Identity, Monad, NoCodeIdentityDebug, Position, UndefinedVariableError}

import java.util
import java.util.UUID

object DebugLogger:

  import maf.core.Monad.MonadSyntaxOps

  private var currentLevel = 0
  private var symbolStack = List("=")

  def log[M[_] : Monad](msg: String): M[Unit] =
    println((0.to(currentLevel)).map(_ => symbolStack.head).mkString("") + " " + msg)
    Monad[M].unit(())

  def enter[M[_] : Monad, X](symbol: String)(c: M[X]): M[X] =
    currentLevel = currentLevel + 1
    symbolStack = symbol :: symbolStack
    c.map(v => {
      currentLevel = currentLevel - 1
      symbolStack = symbolStack.tail
      v
    })

  def enter[M[_] : Monad, X](c: M[X]): M[X] =
    enter(symbolStack.head)(c)

/** This trait encodes the semantics of the ContractScheme language */
trait BaseScvBigStepSemantics extends ScvModAnalysis with ScvBaseSemantics with ScvContextSensitivity with ScvReporter with ScvUpdateCount:
  outer =>

  /** An alias for a closure, which is a combination of a lambda and an environment */
  type Closure = (SchemeLambdaExp, Env)

  import maf.util.FunctionUtils.*
  import maf.core.Monad.MonadSyntaxOps
  import maf.core.Monad.MonadIterableOps
  import maf.core.MonadStateT.{lift, unlift}
  import evalM._
  import scvMonadInstance.impure

  private lazy val `true?`: Prim = primitives.allPrimitives("true?")
  private lazy val `false?`: Prim = primitives.allPrimitives("false?")

  override def intraAnalysis(component: Component): BaseIntraScvSemantics

  /**
   * Looks up the symbolic representation of the given variable, and returns it if it exists. Otherwise, returns a fresh symbolic representation for
   * the variable.
   */
  protected def lookupCache(id: Identifier): EvalM[Option[Symbolic]] =
    for
      env <- getEnv
      addr <- unit(
        env.lookup(id.name).getOrElse(throw Exception(s"variable ${id.name} not found"))
      ) // exception should not happen because of lexical address pass
      value <- lookupCache(addr)
    yield value

  extension (p: Prim)
    def symApply(id: Identity, args: Symbolic*): Symbolic =
      SchemeFuncall(SchemeVar(Identifier(p.name, Identity.none)), args.toList, id)



  var pathConditions: Map[SchemeExp, Set[Formula]] = Map()  //(Mehdi)
  
  trait BaseIntraScvSemantics extends IntraAnalysis with IntraScvAnalysis with BaseIntraAnalysis:

    import DebugLogger.*

    protected val cmp: Component = component

    /**
     * Run the intra semantics using the given initial state
     *
     * @param initialState
     * the initial state of the intra analysis
     * @return
     * a list of possible post values, and a path store
     */
    protected def runIntraSemantics(initialState: State): Set[(PostValue, PathCondition)] =
      val resultsM = for
        _ <- injectCtx
        //_ <- injectPre
        value <- extract(eval(expr(cmp)))
        _ <- checkPost(value)
        ps <- getPc
      yield (value, ps)

      resultsM.runValue(initialState).vs.map(_._2)

    override def analyzeWithTimeout(timeout: Timeout.T): Unit =
      track(NumberOfComponents, cmp)
      count(NumberOfIntra)
      //println(s"Component count ${trackMetrics(NumberOfComponents).size}")

      val initialState = State.empty.copy(env = fnEnv, store = initialStoreCache)
      val answers = runIntraSemantics(initialState)
      answers.map(_._1.value).foreach(writeResult(_, cmp))
    //println(s"done analyzing $cmp")

    /** Check the post contract on the value resulting from the analysis of the current component */
    private def checkPost(value: PostValue): EvalM[Unit] =
      usingRangeContract(cmp) {
        case Some(contract) if true =>
          // TODO: check the monIdn parameter
          applyMon(PostValue.noSymbolic(contract), value, expr(cmp), expr(cmp).idn).flatMap(_ => unit(()))
        case _ => unit(())
      }

    /** Injects information from the components context in the current analysis */
    protected def injectCtx: EvalM[Unit] =
      val context = fromContext(cmp)
      for
      // TODO: there is still something wrong here, if I disable this, things should start to fail but they don't...
        cache <- getStoreCache
        _ <- putStoreCache(cache ++ context.lexStoCache)
        _ <- putPc(context.pathCondition)
        _ <- putVars(context.vars)
        _ <- Monad.sequence(context.symbolic.map {
          case (name, Some(value)) =>
            for
              env <- getEnv
              _ <- env.lookup(name).map(writeSymbolic(_)(value)).getOrElse(unit(value))
            yield ()
          case (_, _) => unit(())
        }.toList)
      yield ()

    /** Injects the pre-condition contracts (if any are available) in the analysis of the current component */
    private def injectPre: EvalM[Unit] =
      usingContract(cmp) {
        case Some(domains, _, args, idn) =>
          for
            postArgs <- argValuesList(cmp).mapM { case (addr, arg) =>
              fresh.flatMap(writeSymbolic(addr)).map(s => PostValue(Some(s), arg))
            }

            _ <- Monad.sequence(
              domains
                .zip(postArgs)
                .zip(args)
                .map { case ((domain, arg), exp) =>
                  applyMon(PostValue.noSymbolic(domain), arg, exp, idn, assumed = true)
                }
            )
          yield ()

        case None => unit(())
      }

    /** Computes an initial store cache based on the set of available Scheme primitives */
    protected lazy val initialStoreCache: StoreCache =
      primitives.allPrimitives.keys
        .map(name => baseEnv.lookup(name).get -> SchemeVar(Identifier(name, Identity.none)))
        .toMap

    protected def symIfFeasible[X](symbolic: Option[Symbolic], prim: Prim, id: Identity)(cmp: => M[X]): M[X] =
      symbolic match
        // if we do not have symbolic information we simply execute cmp (overapproximating)
        case None => cmp
        case Some(sym) =>
          for
          // extend the path condition
            _ <- extendPc(prim.symApply(id, sym))
            // check if the path condition is feasible
            pc <- getPc
            vars <- getVars
            solved = sat.feasible(pc.formula, vars)
            result <- if solved then cmp else void
          yield result

    /** Adds support for checking contracts on primitives */
    protected def checkPrimitiveContract(fexp: SchemeFuncall, fval: Value, args: List[(SchemeExp, PostValue)]): M[Unit] =
      track(ImplicitContract, fexp)
      nondets(
        lattice
          .getPrimitives(fval)
          .map(prim =>
            // fetch the signature
            val signature = OpqOps.signatures(prim)
            val ops = OpqOps.symbolicContracts(signature, args.map(_ => ()))
            // check using the path condition whether the negation of the contracts is ifFeasible
            Monad.sequence(ops.zip(args).map { case (op, (exp, argv)) =>
              // synthesize symbolic call to the contract
              val call = symCall(Some(SchemeVar(Identifier(op.name, Identity.none))), List(argv.symbolic))
              nondet(
                symIfFeasible(call, `true?`, exp.idn) {
                  /* no problem simply continue */
                  unit(())
                },
                symIfFeasible(call, `false?`, exp.idn) {
                  /* contract is invalid */
                  doBlame(ContractValues.Blame(exp.idn, fexp.idn))
                }
              )
            }) >>> unit(())
          )
      )

    protected def doBlame[T](blame: Blame): EvalM[T] =
      impure {
        writeBlame(blame)
      }.flatMap(_ => void)

    /** Adds support for opaque values in primitives */
    private def applyPrimitives(fexp: SchemeFuncall, fval: Value, args: List[(SchemeExp, PostValue)]): M[Value] =
      import MonoidInstances.*
      import maf.util.MonoidImplicits.*
      import maf.core.MonadJoin.MonadJoinIterableSyntax
      import maf.language.scheme.primitives.given
      val simpleArgs = args.map { case (e, pv) => (e, pv.value) }
      val values = simpleArgs.map(_._2)

      for
        _ <- checkPrimitiveContract(fexp, fval, args)
        result <- nondet(
          void,
          if OpqOps.eligible(values) then lattice.getPrimitives(fval).foldMapM(prim => OpqOps.compute(fexp, prim, values, primitives))
          else super.applyPrimitives(fexp, fval, simpleArgs)
        )
      yield result

    /** Applies the given primitive and returns its resulting value */
    protected def applyPrimitive(prim: Prim, args: List[Value]): EvalM[Value] =
      prim.call(SchemeValue(Value.Nil, Identity.none), args)

    /** Evaluates the given lambda expression to a closure, keeps track of the lexical store cache as well */
    override def evalClosure(exp: SchemeLambdaExp): EvalM[Value] =
      for
        lenv <- getEnv.map(_.restrictTo(exp.fv))
        // compute the set of addresses in the free variables of the lambda expression
        freeAddresses = lenv.addrs
        //_ = { println(s"got free addrs $freeAddresses") }
        fullCache <- getStoreCache
        //_ = { println(s"fullcache $fullCache") }
        // remove the other addresses from the store cache
        cache = fullCache.filterKeys(freeAddresses.contains(_)).toMap
        // keep track of the lexical store cache
        _ <- effectful {
          lexicalStoCaches = lexicalStoCaches + ((exp, lenv) -> cache)
        }
        // retrieve the lexical path condition
        pc <- getPc
        // clean it up such that it only contains information about the lexical variables
        cleanedPc = pc.gc(cache.values.toSet)
        // keep track of the lexical pc in the global map
        _ <- effectful {
          lexicalPathConditions = lexicalPathConditions + ((exp, lenv) -> cleanedPc)
        }
        // then we use the evaluation semantics of the parent to obtain the closure itself
        result <- super.evalClosure(exp)
      yield result

    protected def assignPost(
                              id: Identifier,
                              env: Env,
                              vlu: PostValue
                            ): M[Unit] = env.lookup(id.name) match
      case None =>
        println("err!")
        baseEvalM.fail(UndefinedVariableError(id))
      case Some(addr) =>
        extendStoCache(addr, vlu)

    protected def assignPost(bds: List[(Identifier, PostValue)], env: Env): M[Unit] =
      import maf.core.Monad.MonadSyntaxOps
      Monad.sequence(bds.map { case (id, vlu) => assignPost(id, env, vlu) }) >>> baseEvalM.unit(())

    private def bindPost(id: Identifier, env: Env, vlu: PostValue): EvalM[Env] =
      val addr = allocVar(id, component)
      val env2 = env.extend(id.name, addr)
      extendStoCache(addr, vlu).map(_ => env2)

    private def bindPost(bds: List[(Identifier, PostValue)], env: Env): EvalM[Env] =
      import maf.core.Monad.MonadIterableOps
      bds.foldLeftM(env) { case (env, (id, pv)) => bindPost(id, env, pv) }

    override protected def evalLet(bindings: List[(Identifier, SchemeExp)], body: List[SchemeExp]): EvalM[Value] =
      for
        bds <- bindings.mapM { case (id, exp) => extract(eval(exp)).map(vlu => (id, vlu)) }
        res <- withEnvM(env => bindPost(bds, env)) {
          evalSequence(body)
        }
      yield res

    override protected def evalLetStar(bindings: List[(Identifier, SchemeExp)], body: List[SchemeExp]): EvalM[Value] =
      bindings match
        case Nil => evalSequence(body)
        case (id, exp) :: restBds =>
          extract(eval(exp)).flatMap { rhs =>
            withEnvM(env => bindPost(id, env, rhs)) {
              evalLetStar(restBds, body)
            }
          }

    override protected def evalLetRec(bindings: List[(Identifier, SchemeExp)], body: List[SchemeExp]): EvalM[Value] =
      for
        newEnv <- getEnv.flatMap(env => bindings.foldLeftM(env) { case (env2, (id, _)) => bind(id, env2, lattice.bottom) })
        result <- withEnv(_ => newEnv) {
          for
            extEnv <- getEnv
            _ <- bindings.mapM_ { case (id, exp) =>
              extract(eval(exp)).flatMap(value => assignPost(id, extEnv, value))
            }
            res <- evalSequence(body)
          yield res
        }
      yield result


    override def eval(exp: SchemeExp): EvalM[Value] =
      for
        result <- exp match
          // literal Scheme values have a trivial symbolic representation -> their original expression
          case SchemeValue(value, _) => super.eval(exp).flatMap(tag(exp))
          case SchemeVar(nam) => evalVariable(nam)
          case SchemeIf(prd, csq, alt, _) => evalIf(prd, csq, alt)

          // only enabled for testing
          case e@SchemeFuncall(SchemeVar(Identifier("halt", _)), List(), _) if DEBUG =>
            throw new Exception(s"halting occcured at ${e.idn.pos}")

          case e@SchemeFuncall(SchemeVar(Identifier("debug", _)), List(SchemeVar(Identifier("$cmp", _))), _) if DEBUG =>
            for _ <- effectful {
              println(s"debug/cmp: ${e.idn.pos}: $cmp")
            } yield lattice.nil

          case e@SchemeFuncall(SchemeVar(Identifier("debug", _)), List(SchemeVar(Identifier("$pc", _))), _) if DEBUG =>
            for
              pc <- getPc
              _ <- effectful {
                println(s"debug/pc: ${e.idn.pos}: $pc")
              }
            yield lattice.nil
          case SchemeFuncall(SchemeVar(Identifier("debug", _)), List(e), _) if DEBUG =>
            for
              v <- eval(e)
              _ <- effectful {
                println(s"debug: ${e.idn.pos}: $v")
              }
            yield lattice.nil

          // only enabled for testing, results in a nil value associated with a fresh symbol
          case SchemeFuncall(SchemeVar(Identifier("fresh", _)), List(), _) =>
            for
              symbolic <- fresh
              value <- tag(symbolic)(lattice.opq(ContractValues.Opq()))
            yield value

          // function calls have different behaviour in SCV as they can be guarded by contract
          case f@SchemeFuncall(_, _, _) => callFun(f)

          // contract specific evaluation rules
          case ContractSchemeMon(contract, expression, idn) =>
            for
              contractVal <- extract(eval(contract))
              expressionVal <- extract(eval(expression))
              result <- applyMon(contractVal, expressionVal, expression, idn, contractExpr = Some(contract))
            yield result

          case ContractSchemeFlatContract(expression, idn) =>
            extract(eval(expression)).flatMap(pv => unit(lattice.flat(ContractValues.Flat(pv.value, expression, pv.symbolic, idn))))

          case ContractSchemeDepContract(domains, rangeMaker, idn) =>
            for
              evaluatedDomains <- domains.mapM(eval)
              evaluatedRangeMaker <- eval(rangeMaker)
            yield lattice.grd(ContractValues.Grd(evaluatedDomains, evaluatedRangeMaker, domains.map(_.idn), rangeMaker))

          case contractExp@ContractSchemeCheck(_, _, _) =>
            evalCheck(contractExp)

          case MatchExpr(value, clauses, _) =>
            // TODO: same as maf.modularchemeSupport.scv.SchemeContractS see if this can be factored out
            for
              _ <- eval(value) // evaluate value for side effects but ignore result
              evaluatedClauses <- merge(clauses.map(_.expr).map(evalSequence)) // over approximate by evaluating all clauses at once
            yield evaluatedClauses

          // added code to keep track of path conditions (Mehdi)
  //        case e =>
  //          for
  //            result <- super.eval(e)
  //            pc <- getPc
  //            _ = {
  //              pathConditions = pathConditions + (e -> pc)
  //            }
  //          yield result

          // catch-all, dispatching to the default Scheme semantics
          case _ => super.eval(exp)
        pc <- getPc
        _ = {
//            val existingFormula = pathConditions.getOrElse(exp, pc.formula)
//            val newFormula = Disjunction(Set(existingFormula, pc.formula))
            val existingFormulas = pathConditions.getOrElse(exp, Set.empty)
            val newFormulas = existingFormulas ++ Set(pc.formula)
//            println("this is newformula: " + newFormula)
            pathConditions = pathConditions + (exp -> newFormulas)
        }
//        _ = println("this is exp: " + exp + "          this is formula: " +  pc.formula)
      yield result


    override def evalVariable(id: Identifier): EvalM[Value] =
    // the symbolic representation of a variable is the stored symbolic representation or a fresh symbolic variable
      lookupCache(id).flatMap(sym => super.evalVariable(id).flatMap(tag(sym)))

    /** Executes the monadic action `m` if the given condition is feasible */
    private def ifFeasible[X](prim: Prim, cnd: PostValue, id: Identity)(m: EvalM[X]): EvalM[X] =
      for
        primResult <- applyPrimitive(prim, List(cnd.value))
        oldPc <- getPc
//        _ = println(oldPc) // (Mehdi)
        _ <- cnd.symbolic match
          case None => unit(())
          case Some(symbolic) =>
            extendPc(prim.symApply(id, symbolic))

        pc <- getPc
        vars <- getVars
        result <-
          cnd.symbolic match
            case _ if !lattice.isTrue(primResult) =>
              void // if it is not possible according to the lattice, we do not execute "m"
            //case _ if !lattice.isFalse(primResult) =>
            //    // it is impossible that primResult is false, this means that introduced constraint
            //    // is a tautology and does not give any information in the path condition.
            //    putPc(oldPc) >>> m
            case _ if ! {
              count(SATExec); time(Z3Time) {
                sat.feasible(pc.formula, vars)
              }
            } =>
              void // if the path condition is unfeasible we also do not execute "m"
            case _ => m // if we do not have a path condition or neither of the two conditions above is fulfilled we execute "m"
      yield result

    private def symCond(prdValWithSym: PostValue, csq: SchemeExp, alt: SchemeExp, id: Identity): EvalM[Value] =
      val truVal = ifFeasible(`true?`, prdValWithSym, id)(eval(csq))
      val flsVal = ifFeasible(`false?`, prdValWithSym, id)(eval(alt))
      nondet(truVal, flsVal)

    protected def evalCheck(checkExpr: ContractSchemeCheck): EvalM[Value] =
      track(EvalCheck, checkExpr)

      def appl(procedureOrPrimitive: Closure | String, checkExpr: ContractSchemeCheck, vlu: PostValue): EvalM[PostValue] =
        val injV = procedureOrPrimitive match
          case v: Closure => lattice.closure(v)
          case p: String => lattice.primitive(p)

        val optionalTag = procedureOrPrimitive match
          case p: String => Some(SchemeVar(Identifier(p, Identity.none)))
          case _ => None

        for
          result <- extract(
            applyFunPost(
              SchemeFuncall(checkExpr.contract, List(checkExpr.valueExpression), Identity.none),
              injV,
              List((checkExpr.valueExpression, vlu)),
              checkExpr.idn.pos
            ).flatMap(tag(symCall(optionalTag, List(vlu.symbolic))))
          )
        yield result

      for
        contract <- eval(checkExpr.contract)
        value <- extract(eval(checkExpr.valueExpression))

        // TODO: refactor such that most of this code is in applyMon
        flats = lattice.getFlats(contract).map { flat =>
          // TODO: add a tag here such that the result of executing this flat contract also has a symbolic reprsentation
          extract(
            applyFunPost(
              SchemeFuncall(checkExpr.contract, List(checkExpr.valueExpression), Identity.none),
              flat.contract,
              List((checkExpr.valueExpression, value)),
              checkExpr.idn.pos
            ).flatMap(tag(symCall(flat.sym, List(value.symbolic))))
          )
        }

        // coerce procedures and primitives into flat contracts, in this case no wrapping is required and we can directly apply the
        // procedure predicate.
        // TODO: add a tag to lattice.getPrimitives such that the result of this check expression also is symbolically represented
        procedures = ((lattice.getClosures(contract) ++ lattice.getPrimitives(contract)): Set[Closure | String])
          .map(appl(_, checkExpr, value))

        joinedResult <- nondets[PostValue](flats ++ procedures)

        // Since applying the contract on the value does not (always) generate seperate branches,
        // we split the join again here.
        splitResult <- extract(
          nondets(
            ifFeasible(`true?`, joinedResult, checkExpr.valueExpression.idn) {
              unit(lattice.bool(true)) >>= tag(joinedResult.symbolic)
            },
            ifFeasible(`false?`, joinedResult, checkExpr.valueExpression.idn) {
              unit(lattice.bool(false)) >>= tag(joinedResult.symbolic)
            }
          )
        )
        //splitResult = joinedResult
        pc <- getPc
        vlu <- tag(splitResult._1)(splitResult._2)
      yield vlu

    /**
     * The semantics of a "mon" expression.
     *
     * @param contract
     * The evaluated contract
     * @param expression
     * The expression to apply the monitor to
     * @param expr
     * the AST node of the expression to apply the monitor to
     * @param monIdn
     * the identity of the whole monitor expression
     * @param contractExpr
     * the expression of the contract in the monitor expression (if any).
     * @param assumed
     * if true, will ignore the path where the monitor fails
     */
    protected def applyMon(
                            contract: PostValue,
                            expression: PostValue,
                            expr: SchemeExp,
                            monIdn: Identity,
                            assumed: Boolean = false,
                            contractExpr: Option[SchemeExp] = None
                          ): EvalM[Value] =
      track(ContractCheck, (expr, monIdn))
      // We have three distinct possibilities for a "mon" expression:
      // 1. `contract` is a flat contract, or a function (or primitive) that can be treated as such, the result of mon is the value of `expression`
      // 2. `contract` is a dependent contract, in which case `expression` must be a function, the result of `mon` is a guarded function
      // 3. `contract` does not satisfy any of the above conditions, resutling in an error
      val extraFlats = (// closures
        lattice
          .getClosures(contract.value)
          .map(f =>
            val expr = contractExpr.getOrElse(f._1)
            ContractValues.Flat(lattice.closure(f), expr, None, expr.idn)
          )
        ) ++ (/* primitives */ lattice
        .getPrimitives(contract.value)
        .map(p =>
          ContractValues
            .Flat(lattice.primitive(p),
              SchemeVar(Identifier(p, Identity.none)),
              Some(SchemeVar(Identifier(p, Identity.none))),
              Identity.none
            )
        ) ++

        /** struct predicates */
        lattice
          .getStructPredicates(contract.value)
          .map(p =>
            ContractValues.Flat(
              lattice.structPredicate(p), /* synthetic, struct predicates do not need fexp */ SchemeValue(maf.language.sexp.Value.Nil,
                Identity.none
              ),
              None,
              Identity.none
            )
          ))

      val flats = (lattice.getFlats(contract.value) ++ extraFlats).map(c => monFlat(c, expression, expr, monIdn, assumed))
      val guards = lattice.getGrds(contract.value).map(c => monArr(c, expression, expr, monIdn))

      nondets(flats ++ guards)

    protected def symCall(fn: Option[Symbolic], args: List[Option[Symbolic]]): Option[Symbolic] =
      import maf.core.OptionMonad.{given}
      for
        fnSym <- fn
        argsSym <- Monad.sequence(args)
      yield SchemeFuncall(fnSym, argsSym, Identity.none)

    protected def monFlat(
                           contract: ContractValues.Flat[Value],
                           value: PostValue,
                           expr: SchemeExp,
                           monIdn: Identity,
                           assumed: Boolean = false
                         ): EvalM[Value] =
      val call = SchemeFuncall(contract.fexp, List(expr), monIdn)
      val resultSymbolic = symCall(contract.sym, List(value.symbolic))
      val ctx = buildCtx(List(value.symbolic), None, contractCall = true)
      for
      // TODO: find better position information
        result <- nondets(
          applyFunPost(call, contract.contract, List((expr, value)), expr.idn.pos, ctx),
          callFun(PostValue.noSymbolic(contract.contract), List(value))
        )
        pv = PostValue(resultSymbolic, result)
        tru = ifFeasible(`true?`, pv, monIdn) {
          unit(value.value).flatMap(value.symbolic.map(tag).getOrElse(unit))
        }
        fls =
          if (!assumed) then
            ifFeasible(`false?`, pv, monIdn) {
              doBlame[Value](ContractValues.Blame(expr.idn, monIdn))
            }
          else void
        result <- nondet(tru, fls)
      yield result

    protected def debugBlame: EvalM[Unit] =
      if DEBUG then
        for
          pc <- getPc
          m <- getStoreCache
          _ <- effectful {
            println(s"writing blame with $pc and $m")
          }
        yield ()
      else unit(())

    protected def monArr(contract: ContractValues.Grd[Value], value: PostValue, expression: SchemeExp, monIdn: Identity): EvalM[Value] =
    // TODO: check that the value is indeed a function value, otherwise this should result in a blame (also check which blame)
      unit(lattice.arr(ContractValues.Arr(monIdn, expression.idn, contract, value.value)))

    protected def applyArr(fc: SchemeFuncall, fv: PostValue, argsvOpt: Option[List[PostValue]] = None): EvalM[Value] = nondets {
      lattice.getArrs(fv.value).map { arr =>
        track(AppArr, (arr, fc))
        for
          argsV <- argsvOpt.map(unit).getOrElse(fc.args.mapM(eval andThen extract))
          values <- argsV.zip(arr.contract.domain).zip(fc.args).mapM { case ((arg, domain), expr) =>
            applyMon(PostValue.noSymbolic(domain), arg, expr, fc.idn) >>= { res =>
              unit(res)
            }
          }
          pc <- getPc
          // apply the range maker function
          rangeContract <- extract(
            applyFunPost(
              SchemeFuncall(arr.contract.rangeMakerExpr, fc.args, Identity.none),
              arr.contract.rangeMaker,
              fc.args.zip(argsV),
              arr.contract.rangeMakerExpr.idn.pos,
            )
          )
          ctx = buildCtx(argsV.map(_.symbolic), Some(rangeContract.value))
          retV <- extract(
            applyFunPost(
              fc, // syntactic function node
              arr.e, // the function to apply
              fc.args.zip(argsV), // the arguments
              fc.idn.pos, // the position of the function in the source code
              ctx
              //Some(() => ContractCallContext(arr.contract.domain, rangeContract, fc.args, fc.idn))
            )
          ).flatMap {
            case PostValue(None, value) =>
              // if we did not get a symbolic value as a return, we simply tag it with a fresh variable
              fresh.flatMap(e => extract(tag(Some(e))(value)))
            case v => scvMonadInstance.unit(v)
          }
          // we assume the range contract to hold
          _ <- applyMon(rangeContract, retV, fc, fc.idn, true)
        yield retV.value
      }
    }

    /**
     * A hook called by callFun, which can be used to add additional application semantics. For example to support call/cc or other objects that
     * behave like functions
     */
    protected def callFun(f: PostValue, args: List[PostValue]): EvalM[Value] = void

    private def applyFunPost(
                              fexp: SchemeFuncall,
                              fval: Value,
                              args: List[(SchemeExp, PostValue)],
                              cll: Position.Position,
                              ctx: ContextBuilder = DefaultContextBuilder,
                            ): M[Value] =
      // TODO: this is code duplication from SchemeModFSemantics, refactor it so that code duplication is avoided.
      import maf.core.Monad.MonadSyntaxOps
      val simpleArgs = args.map(arg => (arg._1, arg._2.value))
      val fromClosures = applyClosuresM(fval, simpleArgs, cll, ctx)
      val fromPrimitives = applyPrimitives(fexp, fval, args)
      val _ = applyContinuations(fval, simpleArgs)
      baseEvalM.mjoin(List(fromClosures, fromPrimitives)) >>= inject

    private def applyOpq(fv: PostValue, args: List[PostValue]): EvalM[Value] =
    // Applying an opaque function value results in a new opaque value with a fresh identifier
      if lattice.isOpq(fv.value) then
        for
          f <- fresh
          result <- tag(f)(lattice.opq(Opq()))
        yield result
      else void

    private def callFun(f: SchemeFuncall): EvalM[Value] =
      for
        fv <- extract(eval(f.f))
        argsV <- f.args.mapM(eval andThen extract)
        ctx = buildCtx(argsV.map(_.symbolic), None)

        result <- extract(
          if argsV.map(_.value).exists(lattice.isBottom(_)) then void
          else
            nondets(
              applyArr(f, fv, Some(argsV)),
              callFun(fv, argsV),
              applyFunPost(f, fv.value, f.args.zip(argsV), f.idn.pos, ctx),
              applyOpq(fv, argsV)
            ).flatMap(symCall(fv.symbolic, argsV.map(_.symbolic)).map(tag).getOrElse(unit))
        )

        // we then refine booleans, such that they satisfy the path condition
        refinedResult <- refineValue(result, f.f.idn) // manier vinden om id terug te vinden
      yield refinedResult.value

    private def refineValue(result: PostValue, id: Identity): EvalM[PostValue] =
      if lattice.isBoolean(result.value) && result.symbolic.isDefined then
        extract(
          nondets(
            ifFeasible(`true?`, result, id) {
              tag(result.symbolic)(lattice.bool(true))
            },
            ifFeasible(`false?`, result, id) {
              tag(result.symbolic)(lattice.bool(false))
            }, {
              val otherValues = result.value // lattice.retractBool(result.value)
              if lattice.isBottom(otherValues) then void else tag(result.symbolic)(otherValues)
            }
          )
        )
      else unit(result)

    override protected def evalIf(prd: SchemeExp, csq: SchemeExp, alt: SchemeExp): EvalM[Value] =
    // the if expression is evaluated in a different way, because we use symbolic information to extend the path condition and rule out unfeasible paths
      for
        prdValWithSym <- extract(eval(prd))
        ifVal <- symCond(prdValWithSym, csq, alt, prd.idn)
      yield ifVal

  end BaseIntraScvSemantics

end BaseScvBigStepSemantics

trait ScvBigStepSemantics extends BaseScvBigStepSemantics:
  override def intraAnalysis(component: Component): IntraScvSemantics =
    IntraScvSemantics(component)

  class IntraScvSemantics(cmp: Component) extends IntraAnalysis(cmp), BaseIntraScvSemantics
end ScvBigStepSemantics
