package maf.modular.scheme.modactor

import maf.core.monad.*
import maf.modular.scheme.modflocal.EffectsMC
import maf.core.DynMonad
import maf.core.Monad.*
import maf.modular.scheme.modf.*
import maf.modular.scheme.modf.SchemeModFComponent
import maf.util.Monoid
import maf.util.MonoidImplicits.*
import maf.core.Monad
import maf.modular.scheme.modflocal.EffectsStateM
import maf.language.scheme.*
import maf.modular.ModAnalysis
import maf.language.AScheme.ASchemeLattice
import maf.core.Environment
import maf.core.Address
import maf.core.Identifier
import maf.modular.scheme.PtrAddr
import maf.core.Identity
import maf.modular.scheme.modf.SchemeModFComponent
import maf.language.scheme.primitives.SchemePrimitives
import maf.language.AScheme.ASchemeValues.Behavior
import maf.modular.scheme.VarAddr
import maf.util.benchmarks.Timeout.T
import scala.reflect.ClassTag
import maf.modular.Dependency
import maf.core.MonadStateT
import maf.core.monad.ReaderT
import maf.modular.worklist.FIFOWorklistAlgorithm
import maf.core.StateOps
import maf.core.Lattice
import maf.language.AScheme.ASchemeValues.AID
import maf.modular.scheme.SchemeConstantPropagationDomain
import maf.modular.scheme.modf.SchemeModFComponent.Call
import maf.core.worklist.FIFOWorkList
import maf.util.MonoidInstances
import maf.modular.ReturnAddr
import maf.modular.scheme.PrmAddr
import maf.core.IdentityMonad
import maf.util.StoreUtil
import maf.language.AScheme.ASchemeValues
import maf.language.ContractScheme.ContractValues
import maf.language.scheme.lattices.SchemeLattice
import maf.modular.scheme.modactor.*
import maf.util.Default
import maf.lattice.HMap

class GlobalStoreState[Component, M, Mailbox <: AbstractMailbox[M]: Default, Value](using lattice: SchemeLattice[Value, Address]):
    case class IntraState(
        self: Component,
        writes: Set[Dependency] = Set(),
        reads: Set[Dependency] = Set(),
        calls: Set[Component] = Set(),
        mailboxes: Map[Component, Mailbox] = Map(),
        actors: Set[Component] = Set(),
        behaviors: Map[Component, Set[Behavior]] = Map(),
        sto: Map[Address, Value] = Map())

    case class InterState(
        mailboxes: Map[Component, Mailbox] = Map(),
        actors: Set[Component] = Set(),
        behaviors: Map[Component, Set[Behavior]] = Map(),
        sto: Map[Address, Value])

    /** Sync the intra state with the current inter state */
    def sync(intra: IntraState, inter: InterState): InterState =
        // join the global stores together
        val sto = intra.sto.foldLeft(inter.sto) { case (acc, (key, vlu)) =>
            acc + (key -> lattice.join(inter.sto.get(key).getOrElse(lattice.bottom), vlu))
        }

        // println(s"+++++++ sync, sto size ${sto.keys.size}")
        // println(s"+++++++ mailbox size ${intra.mailboxes.values.map(_.messages.size).sum}")

        val newMailboxes = intra.mailboxes
            .foldLeft(inter.mailboxes) { case (mailboxes, (cmp, mailbox)) =>
                val mailboxInter = inter.mailboxes.get(cmp).getOrElse(Default.default)

                mailboxes + (cmp -> mailboxInter.merge(mailbox).asInstanceOf[Mailbox])
            }

        inter.copy(sto = sto,
                   mailboxes = newMailboxes,
                   behaviors = MonoidInstances.mapMonoid.append(inter.behaviors, intra.behaviors),
                   actors = inter.actors ++ intra.actors
        )

trait GlobalStoreModActor extends SchemeModActorSemantics, SimpleMessageMailbox, PowersetMailboxAnalysis, ASchemeConstantPropagationDomain:
    outer =>

    val outerClassTag: ClassTag[Component] = summon[ClassTag[Component]]

    def actorIdComponent(a: AID)(using ClassTag[Component]): Component = a match
        case ActorAnalysisComponent(enclosingActor, _, _) => enclosingActor
        case _                                            => throw new Exception(s"unknown actor id $a")

    protected def enclosing(cmp: Component): Component = cmp match
        case ActorAnalysisComponent(enclosingActor, _, _) => enclosingActor

    type Context = Unit
    override type Component = SchemeModActorComponent[Ctx]

    import maf.core.SetMonad.*

    //type State = IntraState
    //type Inter = InterState

    given defaultMailbox: Default[Mailbox] with
        def default: Mailbox = emptyMailbox

    protected val globalStore = GlobalStoreState[Component, Msg, Mailbox, Value](using defaultMailbox, lattice)

    protected type IntraState = globalStore.IntraState
    protected type InterState = globalStore.InterState

    implicit def viewIntra(intra: Intra): globalStore.IntraState
    implicit def viewInter(inter: Inter): globalStore.InterState
    implicit def injectIntra(intra: globalStore.IntraState): Intra
    implicit def injectInter(inter: globalStore.InterState): Inter

    type Ctx = Context

    //////////////////////////////////////////////////
    // Components
    //////////////////////////////////////////////////

    def initialComponent: Component =
        ActorAnalysisComponent(MainActor, None, Some(()))

    //
    // Body
    //

    private def enclosingActorBody(cmp: SchemeModActorComponent[Ctx]): SchemeExp = cmp match
        // the main actor is represented by the main Scheme program
        case MainActor => program
        // otherwise we analyze the body of the behavior of the actor
        case Actor(beh, env, ctx) => beh.bdy
        // All other cases are either not supported or already caught by `body`
        case _ => throw new Exception(s"component $cmp is not supported")

    private def sequentialComponentBody(cmp: SchemeModFComponent): SchemeExp = cmp match
        // A component associated with a regular function call
        case Call((clo, _), _) => SchemeBegin(clo.body, Identity.none)
        // A component associated with the behavior of an actor
        case BehaviorComponent(beh, _, _) => beh.bdy
        // All other cases are either not supported or already caught by `body`
        case _ => throw new Exception(s"component $cmp is not supported.")

    override def body(cmp: Component): SchemeExp = cmp match
        // the initial behavior of an actor
        case ActorAnalysisComponent(enclosingActor, None | Some(SchemeModFComponent.Main), _) =>
            enclosingActorBody(enclosingActor)
        // a function or a new behavior of the actor
        case ActorAnalysisComponent(enclosingActor, Some(sequential), _) =>
            sequentialComponentBody(sequential)

    //
    // Context
    //

    override def componentContext(cmp: Component): Ctx = cmp match
        // the initial behavior of an actor
        case ActorAnalysisComponent(_, _, ctx) =>
            ctx.get

    override def initialCtx: Ctx = ()

    override def newContext(fex: Exp, lam: Lam, ags: List[Val], ctx: Ctx): Ctx = ()

    //
    // Env
    //

    def environment(cmp: Component): Env =
        cmp match
            case ActorAnalysisComponent(MainActor, None | Some(SchemeModFComponent.Main), _) => initialEnv
            case ActorAnalysisComponent(Actor(beh, env, ctx), None | Some(SchemeModFComponent.Main), _) =>
                env
            case ActorAnalysisComponent(_, Some(SchemeModFComponent.Call(clo, ctx)), _) =>
                clo._2
            case ActorAnalysisComponent(_, Some(BehaviorComponent(beh, env, ctx)), _) =>
                env

    //////////////////////////////////////////////////
    // Results
    //////////////////////////////////////////////////

    override def getBehaviors: Map[Component, Set[Behavior]] =
        _result.nn.behaviors

    override def getMailboxes: Map[Component, Mailbox] =
        _result.nn.mailboxes

    override def printResult: Unit =
        println(StoreUtil.storeString(_result.nn.sto))
        println(s"Number of spawned actors ${_result.nn.actors.size}")
        println(s"Number of message sends ${_result.nn.mailboxes.values.map(_.messages.size).sum}")

    //////////////////////////////////////////////////
    // ModAnalysis
    //////////////////////////////////////////////////

    // TODO: abstract this in a seperate trait, and provide a mixin
    override val emptyWorklist = FIFOWorkList.empty

    override lazy val initialInterState: Inter =
        // TODO: to not use implicit conversion but provide explicit one
        globalStore.InterState(sto = initialSto)

    override lazy val initialEnv: Env =
        Environment(primitives.allPrimitives.map { case (name, vlu) =>
            name -> PrmAddr(name)
        })

    override lazy val initialSto: Map[Address, Value] =
        primitives.allPrimitives.map { case (name, vlu) =>
            PrmAddr(name) -> lattice.primitive(name)
        }.toMap

    override def injectInter(inter: Inter, cmp: Component): DynMonad[Value, EffectsMC[Component, Intra]] =
        import analysisM.*
        val m: A[Value] = for
            // insert the store into the analysis
            _ <- get.map(lens.modify(lens.sto)(_ => inter.sto)) >>= put
            // put the correct mailbox
            _ <- get.map(lens.modify(lens.mailboxes)(_ => inter.mailboxes)) >>= put
            // then evalute the expression
            v <- eval(body(cmp))
            // write the value to the global store at its return address
            _ <- updateSto(ReturnAddr(cmp, Identity.none), v)
        yield v

        DynMonad.from(m)

    def syncInter(intra: Intra, inter: Inter): Inter =
        // TODO: do not use implicit conversion to Inter/Intra here
        globalStore.sync(intra, inter)

    //////////////////////////////////////////////////
    // Monad Instance
    //////////////////////////////////////////////////

    type Reader = [Y] =>> ReaderT[EitherT_[Intra][Set], (Ctx, Env), Y]
    type A[X] = MonadStateT[Intra, Reader, X]

    given lens: ActorLens[Intra] = new ActorLens[Intra] {
        //
        // Store
        //
        def putSto(st: Intra, sto: Map[Address, Value]): Intra =
            st.copy(sto = sto)
        def getSto(st: Intra): Map[Address, Value] =
            st.sto

        //
        // Mailboxes
        //
        def putMailboxes(st: Intra, mb: Map[Component, Mailbox]): Intra =
            st.copy(mailboxes = mb)
        def getMailboxes(st: Intra): Map[Component, Mailbox] =
            st.mailboxes

        //
        // Set of actors spawned
        //
        def putActors(st: Intra, actors: Set[Component]): Intra =
            st.copy(actors = actors)
        def getActors(st: Intra): Set[Component] =
            st.actors

        //
        // Set of behaviors discovered during the sequential intra-analysis
        //
        def putBehaviors(st: Intra, behs: Map[Component, Set[Behavior]]): Intra =
            st.copy(behaviors = behs)
        def getBehaviors(st: Intra): Map[Component, Set[Behavior]] =
            st.behaviors

        /** "write" effects */
        def putWrites(s: Intra, w: Set[Dependency]): Intra =
            s.copy(writes = w)
        def getWrites(s: Intra): Set[Dependency] =
            s.writes

        /** "read" effects */
        def putReads(s: Intra, w: Set[Dependency]): Intra =
            s.copy(reads = w)
        def getReads(s: Intra): Set[Dependency] =
            s.reads

        /** "call" effects */
        def putCalls(s: Intra, c: Set[Component]): Intra =
            s.copy(calls = c)
        def getCalls(s: Intra): Set[Component] = s.calls

        /** access to a field called "self" */
        def getSelfCmp(s: Intra): Component =
            s.self
    }

    protected val monadInstance: StateOps[Intra, A] = MonadStateT.stateInstance[Intra, Reader]
    implicit val analysisM = new ModularAnalysisM with EffectsStateM[A, Component, Intra] {
        given componentGiven: ClassTag[Component] = outer.outerClassTag

        export monadInstance.*
        import monadInstance.*
        import maf.core.monad.MonadLift.*
        def getEnv: A[Env] = map(lift(ReaderT.ask))(_._2)
        def getCtx: A[Ctx] = map(lift(ReaderT.ask))(_._1)
        def selfActor: A[ActorRef] = selfActorCmp.map { case a @ ActorAnalysisComponent(enclosing, _, _) =>
            enclosing match
                case MainActor =>
                    ASchemeValues.Actor(Some("name"), a)
                case Actor(beh, _, _) =>
                    ASchemeValues.Actor(beh.name, a)
                case _ => throw new Exception("cannot enclose an enclosing actor into an enclosing actor")
        }
        def selfActorCmp: A[Component] =
            get.map(_.self)
        def mbottom[X]: A[X] =
            get.flatMap(state => lift(ReaderT.lift(EitherT(Set(Left(state))))))

        def mjoin[X: Lattice](x: A[X], y: A[X]): A[X] =
            // in this lattice we do not join
            nondets(List(x, y))
        def allocateCall(lam: Lam, env: Environment[Address]): A[Component] =
            for
                ctx <- getCtx
                cmp <- selfActorCmp
            yield ActorAnalysisComponent(enclosing(cmp), Some(SchemeModFComponent.Call((lam, env), None)), Some(ctx))

        def allocateBehavior(beh: Behavior, idn: Identity): A[Component] =
            for
                // TODO: allocate some context
                ctx <- getCtx
                cmp <- selfActorCmp
                // TODO: expand environment? check with the code in the semantics
                env <- getEnv
            yield ActorAnalysisComponent(enclosing(cmp), Some(BehaviorComponent(beh, env, None)), Some(ctx))

        def allocateActor(initialBehavior: Behavior, idn: Identity): A[Component] =
            for
                ctx <- getCtx
                env <- getEnv
            yield ActorAnalysisComponent(Actor(initialBehavior, env, ()), None, Some(ctx))

        def allocateEmpheralChild(component: Component, m: Msg): A[Component] =
            unit(EmpheralChildComponent[Ctx, Msg](component, m))

        def nondets[X](xs: Iterable[A[X]]): A[X] =
            MonadStateT((s) =>
                ReaderT((e) =>
                    EitherT({
                        val result = xs.toList.foldMap(_.run(s).runReader(e).runEither)
                        if result.isEmpty then Set(Left(s)) else result
                    })
                )
            )

        def withEnv[X](f: Env => Env)(blk: A[X]): A[X] =
            import maf.core.SetMonad.*
            MonadStateT((s) =>
                ReaderT.local[EitherT_[Intra][Set], (Ctx, Env), (X, Intra)] { case (ctx, env: Env) => (ctx, f(env)) }(
                  blk.run(s)
                )
            )

        def withCtx[X](f: Ctx => Ctx)(blk: A[X]): A[X] =
            import maf.core.SetMonad.*
            MonadStateT((s) =>
                ReaderT.local[EitherT_[Intra][Set], (Ctx, Env), (X, Intra)] { case (ctx, env: Env) => (f(ctx), env) }(
                  blk.run(s)
                )
            )

        def fail[X](err: maf.core.Error): A[X] = { println(s"failing with $err"); mbottom }

        /**
         * Runs the analysis represented by `m` for the given `cmp`.
         *
         * @note
         *   it is expected that `m` is a computation that injects the correct store and environment
         */
        def run(cmp: Component, m: A[Unit]): Set[Intra] =
            // TODO: for `st` do not use implicit wrapping using injectIntra, but provide explicit one.
            val st = globalStore.IntraState(self = cmp)
            val ev = (componentContext(cmp), environment(cmp))
            m.run(st).runReader(ev).runEither.map {
                case Left(s)       => s
                case Right((_, s)) => s
            }

    }

    override def view(cmp: Component): SchemeModActorComponent[Context] = cmp match
        case ActorAnalysisComponent(enclosing, _, _) => ActorAnalysisComponent(enclosing, None, None)
        case a: Actor[_]                             => ActorAnalysisComponent(a, None, None)
        case MainActor                               => ActorAnalysisComponent(MainActor, None, None)
end GlobalStoreModActor

class SimpleGlobalStoreModActor(prog: SchemeExp) extends SchemeModActorSemantics(prog), GlobalStoreModActor:
    type State = IntraState
    type Inter = InterState

    implicit def viewIntra(intra: Intra): globalStore.IntraState = intra
    implicit def viewInter(inter: Inter): globalStore.InterState = inter
    implicit def injectIntra(intra: globalStore.IntraState): Intra = intra
    implicit def injectInter(inter: globalStore.InterState): Inter = inter
