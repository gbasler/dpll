import scala.collection.mutable

trait Logic {

  trait PropositionalLogic {
    type Type
    type Tree

    class Prop

    type Const

    type TypeConst <: Const

    trait TypeConstExtractor {
      def apply(tp: Type): Const
    }

    type ValueConst <: Const

    trait ValueConstExtractor {
      def apply(p: Tree): Const
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
