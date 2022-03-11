package maf.modular.scv

import maf.core.*
import maf.core.Position.*
import maf.language.scheme.*
import maf.modular.scheme.modf.*

/*
 * Soft contract verification uses the following forms of
 * context:
 *
 * - Contract call: if a function that is beinig monitored by a particular
 *   contract is called, the pre-condition and post-condition contracts
 *   are part of the context, and can be used during the analysis such
 *   that the preconditions can be assumed, and the post-condition
 *   can be checked, after the analysis of a particular component
 * - k-path conditions: during the analysis, the path conditions
 *    from the previous "k" components are added to the context
 *    to enable more precise symbolic information to be available during the
 *    analysis.
 */
sealed trait ScvContext[L]

/** Used when the function call is originating from applying a monitor */
case class ContractCallContext[L](domains: List[L], rangeContract: L, args: List[SchemeExp], idn: Identity) extends ScvContext[L]

trait ScvContextSensitivity extends SchemeModFSensitivity:
    type ComponentContext = ScvContext[Value]

    /**
     * Keeps track of the path conditions from the last k components
     *
     * @param pc
     *   a list of path conditions from the last k components
     * @param vars
     *   a list of variables used in the path conditions from the last k components
     * @param symbolic
     *   a mapping between names of variables and symbolic values that should be passed between components (also from the last k components)
     * @param changes
     *   a list of changes applied to obtain the current path condition
     * @param symArgs
     *   a list of (symbolic) arguments of the called function (TODO: this might not be a great place to add this)
     */
    // TODO: factor out rangeContract, because it is required for a sound implementation of scv, and cannot be disabled/enabled
    // for certain experiments.As such it is not part of a variable context.
    case class KPathCondition[L](
        ps: PathStore,
        sstore: SymbolicStore,
        rangeContract: Option[L],
        callers: List[Position],
        changes: List[SymChange],
        symArgs: List[SchemeExp])
        extends ScvContext[L]:
        override def toString: String = s"KPathCondition(rangeContract = $rangeContract, pc = ${ps.pc}, sstore = $sstore)"
    case class NoContext[L]() extends ScvContext[L]

    def contractContext(cmp: Component): Option[ContractCallContext[Value]] = context(cmp).flatMap {
      case c: ContractCallContext[_] =>
        // safety: the ComponentContext is constrained to ScvContext[Value] (where
        // the type paremeter is invariant) which
        // means that ContractCallContext is always in L = Value otherwise
        // it does not type check. But unfortunately type parameters are erased
        // at runtime, and the isInstanceOf check cannot garuantee the type
        //  of the type parameter at runtime.
        Some(c.asInstanceOf[ContractCallContext[Value]])

      case _ => None
    }

    override def allocCtx(
        clo: (SchemeLambdaExp, Environment[Address]),
        args: List[Value],
        call: Position,
        caller: Component
      ): ComponentContext = NoContext() // contexts will be created by overriding them in the semantics

trait ScvKContextSensitivity extends ScvContextSensitivity with ScvModAnalysis:
    import evalM.*
    import maf.core.Monad.MonadSyntaxOps

    protected def k: Int
    protected def m: Int

    protected def usingContract[X](cmp: Component)(f: Option[(List[Value], Value, List[SchemeExp], Identity)] => X): X = contractContext(cmp) match
        case Some(context) => f(Some(context.domains, context.rangeContract, context.args, context.idn))
        case _             => f(None)

    protected def usingRangeContract[X](cmp: Component)(f: Option[Value] => X): X = context(cmp) match
        case Some(KPathCondition(_, _, rangeContractOpt, _, _, _)) => f(rangeContractOpt)
        case _                                                     => f(None)

    override def fromContext(cmp: Component): FromContext = context(cmp) match
        case Some(KPathCondition(ps, sstore, _, cmps, _, _)) =>
          new FromContext:
              def pathCondition: List[SchemeExp] = ps.pc
              def vars: List[String] = ps.vars
              def symbolic: Map[String, Option[SchemeExp]] =
                sstore.mapping.mapValues(sym => Some(sym.expr)).toMap.withDefaultValue(None)
        case _ => EmptyContext

    override def buildCtx(symArgs: List[Option[SchemeExp]], rangeContract: Option[Value] = None): ContextBuilder =
      new ContextBuilder:
          def allocM(
              clo: (SchemeLambdaExp, Environment[Address]),
              args: List[Value],
              call: Position,
              caller: Component
            ): EvalM[ComponentContext] =
              // TODO: put free variables and their possible sybolic representation in the map as well
              val symbolic = clo._1 match
                  case SchemeLambda(_, prs, _, _, _)          => prs.map(_.name).zip(symArgs)
                  case SchemeVarArgLambda(_, prs, _, _, _, _) => prs.map(_.name).zip(symArgs.take(prs.length))

              val roots = Symbolic.identifiers(symArgs.flatten)

              val nextCallers = (context(caller) match
                  case Some(KPathCondition(_, _, _, callers, _, _)) =>
                    (call :: callers)
                  case _ => List(call)
              ).take(m)

              for
                  ps <- getPathStore
                  vars <- getVars
                  _ = { println(s"got $ps and $vars for applying $clo with $args at $call") }

                  result <- SymbolicStore()
                    .addAll(symbolic.flatMap { case (vr, sym) =>
                              sym.map(vr -> Symbolic(_))
                            },
                            fresh,
                            SymbolicStore.onlyVarsAllowed
                    )
                  (sstore, changes) = result

                  cleanedPs = ps.clean(changes)
                  psGc = cleanedPs.gc(sstore.roots)
                  lowest = psGc.lowest
                  newPs = psGc.reindex(lowest)
                  newSstore = sstore.gc(cleanedPs.pc).reindex(lowest)
              yield KPathCondition[Value](newPs,
                                          newSstore,
                                          rangeContract,
                                          nextCallers,
                                          changes,
                                          symArgs.flatMap(_.map(List(_)).getOrElse(List())).toList
              )

trait ScvOneContextSensitivity(protected val m: Int) extends ScvKContextSensitivity:
    protected val k: Int = 1
