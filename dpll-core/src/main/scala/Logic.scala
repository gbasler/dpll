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

    final case class And(ops: Set[Prop]) extends Prop

    object And {
      def apply(ops: Prop*) = new And(ops.toSet)
    }

    final case class Or(ops: Set[Prop]) extends Prop

    object Or {
      def apply(ops: Prop*) = new Or(ops.toSet)
    }

    case class Not(a: Prop) extends Prop

    case object True extends Prop

    case object False extends Prop

    // symbols are propositions
    class Sym(val variable: String) extends Prop {
      val id: Int = Sym.nextSymId

      override def hashCode(): Int = {
        variable.##
      }

      override def equals(other: scala.Any): Boolean = other match {
        case that: Sym => variable == that.variable
        case _ => false
      }

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

    /**
     * Simplifies propositional formula according to the following rules:
     * - eliminate double negation (avoids unnecessary Tseitin variables)
     * - flatten trees of same connectives (avoids unnecessary Tseitin variables)
     * - removes constants and connectives that are in fact constant because of their operands
     * - eliminates duplicate operands
     * - convert into NNF
     *
     * Complexity: DFS over formula tree
     *
     * See http://www.decision-procedures.org/slides/propositional_logic-2x3.pdf
     */
    def simplify(f: Prop): Prop = {

      // limit size to avoid blow up
      def hasImpureAtom(ops: Seq[Prop]): Boolean = ops.size < 10 &&
        ops.combinations(2).exists {
          case Seq(a, Not(b)) if a == b => true
          case Seq(Not(a), b) if a == b => true
          case _                        => false
        }

      // push negation inside formula
      def negationNormalFormNot(p: Prop): Prop = p match {
        case And(ops) => Or(ops.map(negationNormalFormNot)) // De'Morgan
        case Or(ops)  => And(ops.map(negationNormalFormNot)) // De'Morgan
        case Not(p)   => negationNormalForm(p)
        case True     => False
        case False    => True
        case s: Sym   => Not(s)
      }

      def negationNormalForm(p: Prop): Prop = p match {
        case And(ops)     => And(ops.map(negationNormalForm))
        case Or(ops)      => Or(ops.map(negationNormalForm))
        case Not(negated) => negationNormalFormNot(negated)
        case True
             | False
             | (_: Sym)   => p
      }

      def simplifyProp(p: Prop): Prop = p match {
        case And(fv)     =>
          // recurse for nested And (pulls all Ands up)
          val ops = fv.map(simplifyProp) - True // ignore `True`

          // build up Set in order to remove duplicates
          val opsFlattened = ops.flatMap {
            case And(fv) => fv
            case f       => Set(f)
          }.toSeq

          if (hasImpureAtom(opsFlattened) || opsFlattened.contains(False)) {
            False
          } else {
            opsFlattened match {
              case Seq()  => True
              case Seq(f) => f
              case ops    => And(ops: _*)
            }
          }
        case Or(fv)      =>
          // recurse for nested Or (pulls all Ors up)
          val ops = fv.map(simplifyProp) - False // ignore `False`

          val opsFlattened = ops.flatMap {
            case Or(fv) => fv
            case f      => Set(f)
          }.toSeq

          if (hasImpureAtom(opsFlattened) || opsFlattened.contains(True)) {
            True
          } else {
            opsFlattened match {
              case Seq()  => False
              case Seq(f) => f
              case ops    => Or(ops: _*)
            }
          }
        case Not(Not(a)) =>
          simplify(a)
        case Not(p)      =>
          Not(simplify(p))
        case p           =>
          p
      }

      val nnf = negationNormalForm(f)
      simplifyProp(nnf)
    }

    trait PropTraverser {
      def apply(x: Prop): Unit = x match {
        case And(ops) => ops foreach apply
        case Or(ops) => ops foreach apply
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
        case And(ops) => And(ops map apply)
        case Or(ops) => Or(ops map apply)
        case Not(a) => Not(apply(a))
        case p => p
      }
    }

    type Solvable

    def eqFreePropToSolvable(f: Prop, fail: Boolean = false): Solvable

    type Model = Map[Sym, Boolean]
    val EmptyModel: Model
    val NoModel: Model

        // this model contains the auxiliary variables as well
    type TseitinModel = collection.immutable.SortedSet[Lit]
    val EmptyTseitinModel = collection.immutable.SortedSet.empty[Lit]
    val NoTseitinModel: TseitinModel = null

    def findModelFor(solvable: Solvable): Model

    def findAllModelsFor(solvable: Solvable): List[Model]
  }

}

trait ScalaLogic extends  Logic  {
  trait TreesAndTypesDomain extends PropositionalLogic  {

  }
}

