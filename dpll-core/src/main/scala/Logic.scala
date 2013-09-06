import scala.collection.mutable

trait Logic {

  trait PropositionalLogic {
    type Type
    type Tree

    class Prop
    case class Eq(p: Var, q: Const) extends Prop

    type Const = String

    type TypeConst <: Const

    trait TypeConstExtractor {
      def apply(tp: Type): Const
    }

    type ValueConst <: Const

    trait ValueConstExtractor {
      def apply(p: Tree): Const
    }

    val NullConst: Const

    type Var <: AbsVar

    trait AbsVar {
      // indicate we may later require a prop for V = C
      def registerEquality(c: Const): Unit

      // call this to indicate null is part of the domain
      def registerNull(): Unit

      // can this variable be null?
      def mayBeNull: Boolean

      // compute the domain and return it (call registerNull first!)
      def domainSyms: Option[Set[Sym]]

      // the symbol for this variable being equal to its statically known type
      // (only available if registerEquality has been called for that type before)
      def symForStaticTp: Option[Sym]

      // for this var, call it V, turn V = C into the equivalent proposition in boolean logic
      // registerEquality(c) must have been called prior to this call
      // in fact, all equalities relevant to this variable must have been registered
      def propForEqualsTo(c: Const): Prop

      // populated by registerEquality
      // once implications has been called, must not call registerEquality anymore
      def implications: List[(Sym, List[Sym], List[Sym])]
    }

    case class And(a: Prop, b: Prop) extends Prop

    case class Or(a: Prop, b: Prop) extends Prop

    case class Not(a: Prop) extends Prop

    case object True extends Prop

    case object False extends Prop

    // symbols are propositions
    case class Sym(variable: String) extends Prop {
      override def toString = variable
    }

    trait PropTraverser {
      def apply(x: Prop): Unit = x match {
        case And(a, b) => apply(a); apply(b)
        case Or(a, b) => apply(a); apply(b)
        case Not(a) => apply(a)
        case Eq(a, b) => applyVar(a); applyConst(b)
        case _ =>
      }
      def applyVar(x: Var): Unit = {}
      def applyConst(x: Const): Unit = {}
    }

    def gatherVariables(p: Prop): Set[Var] = {
      val vars = new mutable.HashSet[Var]()
      (new PropTraverser {
        override def applyVar(v: Var) = vars += v
      })(p)
      vars.toSet
    }

    trait PropMap {
      def apply(x: Prop): Prop = x match { // TODO: mapConserve
        case And(a, b) => And(apply(a), apply(b))
        case Or(a, b) => Or(apply(a), apply(b))
        case Not(a) => Not(apply(a))
        case p => p
      }
    }

        // convert finite domain propositional logic with subtyping to pure boolean propositional logic
    // a type test or a value equality test are modelled as a variable being equal to some constant
    // a variable V may be assigned multiple constants, as long as they do not contradict each other
    // according to subtyping, e.g., V = ConstantType(1) and V = Int are valid assignments
    // we rewrite V = C to a fresh boolean symbol, and model what we know about the variable's domain
    // in a prelude (the equality axioms)
    //   1. a variable with a closed domain (of a sealed type) must be assigned one of the instantiatable types in its domain
    //   2. for each variable V in props, and each constant C it is compared to,
    //      compute which assignments imply each other (as in the example above: V = 1 implies V = Int)
    //      and which assignments are mutually exclusive (V = String implies -(V = Int))
    //
    // note that this is a conservative approximation: V = Constant(A) and V = Constant(B)
    // are considered mutually exclusive (and thus both cases are considered reachable in {case A => case B =>}),
    // even though A may be equal to B   (and thus the second case is not "dynamically reachable")
    //
    // TODO: for V1 representing x1 and V2 standing for x1.head, encode that
    //       V1 = Nil implies -(V2 = Ci) for all Ci in V2's domain (i.e., it is unassignable)
    // may throw an AnalysisBudget.Exception
    def removeVarEq(props: List[Prop], modelNull: Boolean = false): (Formula, List[Formula]) = {

      val vars = new scala.collection.mutable.HashSet[Var]

      object gatherEqualities extends PropTraverser {
        override def apply(p: Prop) = p match {
          case Eq(v, c) =>
            vars += v
            v.registerEquality(c)
          case _ => super.apply(p)
        }
      }

      object rewriteEqualsToProp extends PropMap {
        override def apply(p: Prop) = p match {
          case Eq(v, c) => v.propForEqualsTo(c)
          case _ => super.apply(p)
        }
      }

      props foreach gatherEqualities.apply
      if (modelNull) vars foreach (_.registerNull())

      val pure = props map (p => eqFreePropToSolvable(rewriteEqualsToProp(p)))

      val eqAxioms = formulaBuilder
      @inline def addAxiom(p: Prop) = addFormula(eqAxioms, eqFreePropToSolvable(p))

//      debug.patmat("removeVarEq vars: "+ vars)
      vars.foreach { v =>
        // if v.domainSyms.isEmpty, we must consider the domain to be infinite
        // otherwise, since the domain fully partitions the type of the value,
        // exactly one of the types (and whatever it implies, imposed separately) must be chosen
        // consider X ::= A | B | C, and A => B
        // coverage is formulated as: A \/ B \/ C and the implications are
        v.domainSyms foreach { dsyms => addAxiom(\/(dsyms)) }

        // when this variable cannot be null the equality corresponding to the type test `(x: T)`, where T is x's static type,
        // is always true; when the variable may be null we use the implication `(x != null) => (x: T)` for the axiom
        v.symForStaticTp foreach { symForStaticTp =>
          if (v.mayBeNull) addAxiom(Or(v.propForEqualsTo(NullConst), symForStaticTp))
          else addAxiom(symForStaticTp)
        }

        v.implications foreach { case (sym, implied, excluded) =>
          // when sym is true, what must hold...
          implied  foreach (impliedSym  => addAxiom(Or(Not(sym), impliedSym)))
          // ... and what must not?
          excluded foreach (excludedSym => addAxiom(Or(Not(sym), Not(excludedSym))))
        }
      }

//      debug.patmat("eqAxioms:\n"+ cnfString(toFormula(eqAxioms)))
//      debug.patmat("pure:"+ pure.map(p => cnfString(p)).mkString("\n"))

      (toFormula(eqAxioms), pure)
    }


    // an interface that should be suitable for feeding a SAT solver when the time comes
    type Formula
    type FormulaBuilder

    // creates an empty formula builder to which more formulae can be added
    def formulaBuilder: FormulaBuilder

    // val f = formulaBuilder; addFormula(f, f1); ... addFormula(f, fN)
    // toFormula(f) == andFormula(f1, andFormula(..., fN))
    def addFormula(buff: FormulaBuilder, f: Formula): Unit

    def toFormula(buff: FormulaBuilder): Formula

    // the conjunction of formulae `a` and `b`
    def andFormula(a: Formula, b: Formula): Formula

    // equivalent formula to `a`, but simplified in a lightweight way (drop duplicate clauses)
    def simplifyFormula(a: Formula): Formula

    // may throw an AnalysisBudget.Exception
    def eqFreePropToSolvable(p: Prop): Formula

    type Model = Map[Sym, Boolean]
    val EmptyModel: Model
    val NoModel: Model

    def findModelFor(f: Formula): Model

    def findAllModelsFor(f: Formula): List[Model]
  }

}

trait ScalaLogic extends  Logic  {
  trait TreesAndTypesDomain extends PropositionalLogic  {

    // resets hash consing -- only supposed to be called by TreeMakersToProps
    def prepareNewAnalysis(): Unit = { Var.resetUniques(); Const.resetUniques() }

    object Var extends VarExtractor {
      private var _nextId = 0
      def nextId = {_nextId += 1; _nextId}

      def resetUniques() = {_nextId = 0; uniques.clear()}
      private val uniques = new mutable.HashMap[Tree, Var]
      def apply(x: Tree): Var = uniques getOrElseUpdate(x, new Var(x, x.tpe))
      def unapply(v: Var) = Some(v.path)
    }

    class Var(val path: Tree, staticTp: Type) extends AbsVar {
      private[this] val id: Int = Var.nextId

      // private[this] var canModify: Option[Array[StackTraceElement]] = None
      private[this] def ensureCanModify() = {} //if (canModify.nonEmpty) debug.patmat("BUG!"+ this +" modified after having been observed: "+ canModify.get.mkString("\n"))

      private[this] def observed() = {} //canModify = Some(Thread.currentThread.getStackTrace)

      // don't access until all potential equalities have been registered using registerEquality
      private[this] val symForEqualsTo = new mutable.HashMap[Const, Sym]

      // when looking at the domain, we only care about types we can check at run time
      val staticTpCheckable: Type = checkableType(staticTp)

      private[this] var _mayBeNull = false
      def registerNull(): Unit = { ensureCanModify(); if (NullTp <:< staticTpCheckable) _mayBeNull = true }
      def mayBeNull: Boolean = _mayBeNull

      // populate equalitySyms
      // don't care about the result, but want only one fresh symbol per distinct constant c
      def registerEquality(c: Const): Unit = {ensureCanModify(); symForEqualsTo getOrElseUpdate(c, Sym(this, c))}

      // return the symbol that represents this variable being equal to the constant `c`, if it exists, otherwise False (for robustness)
      // (registerEquality(c) must have been called prior, either when constructing the domain or from outside)
      def propForEqualsTo(c: Const): Prop = {observed(); symForEqualsTo.getOrElse(c, False)}

      // don't access until all potential equalities have been registered using registerEquality
      private lazy val equalitySyms = {observed(); symForEqualsTo.values.toList}

      override def toString = "V"+ id
    }

    sealed abstract class Const {
      def tp: Type
      def wideTp: Type

      def isAny = wideTp.typeSymbol == AnyClass
      def isValue: Boolean //= tp.isStable

      // note: use reference equality on Const since they're hash-consed (doing type equality all the time is too expensive)
      // the equals inherited from AnyRef does just this
    }
  }
}

