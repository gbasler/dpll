import scala.collection.mutable

trait Logic {

  private def max(xs: Seq[Int]) = if (xs isEmpty) 0 else xs max
  private def alignedColumns(cols: Seq[Any]): Seq[String] = {
    def toString(x: Any) = if (x == null) "" else x.toString
    if (cols.isEmpty || cols.tails.isEmpty) cols map toString
    else {
      val colLens = cols map (c => toString(c).length)
      val maxLen = max(colLens)
      val avgLen = colLens.sum/colLens.length
      val goalLen = maxLen min avgLen*2
      def pad(s: String) = {
        val toAdd = ((goalLen - s.length) max 0) + 2
        (" " * (toAdd/2)) + s + (" " * (toAdd/2 + (toAdd%2)))
      }
      cols map (x => pad(toString(x)))
    }
  }

  def alignAcrossRows(xss: List[List[Any]], sep: String, lineSep: String = "\n"): String = {
    val maxLen = max(xss map (_.length))
    val padded = xss map (xs => xs ++ List.fill(maxLen - xs.length)(null))
    padded.transpose.map(alignedColumns).transpose map (_.mkString(sep)) mkString(lineSep)
  }

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
    class Sym(variable: String) extends Prop {
      val id: Int = Sym.nextSymId

      override def toString = variable + "#" + id
    }

    object Sym {
      private val uniques: mutable.HashSet[Sym] = new mutable.HashSet()
      def apply(variable: String): Sym = {
        val newSym = new Sym(variable)
        uniques.find(_ == newSym).getOrElse{
          uniques += newSym
          newSym
        }
      }
      private def nextSymId = {_symId += 1; _symId}; private var _symId = 0
      implicit val SymOrdering: Ordering[Sym] = Ordering.by(_.id)
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

    type Model = collection.immutable.SortedMap[Sym, Boolean]
    val EmptyModel: Model
    val NoModel: Model

    def findModelFor(f: Formula): Model

    def findAllModelsFor(f: Formula): List[Model]
  }

}

trait ScalaLogic extends  Logic  {
  trait TreesAndTypesDomain extends PropositionalLogic  {

  }
}

