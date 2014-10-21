import Collections._
import org.sat4j.core.Vec
import org.sat4j.core.VecInt
import org.sat4j.minisat.SolverFactory
import org.sat4j.specs.ContradictionException
import org.sat4j.specs.ISolver
import org.sat4j.specs.IVec
import org.sat4j.specs.IVecInt
import org.sat4j.specs.TimeoutException
import org.sat4j.tools.ModelIterator

import scala.annotation.tailrec
import scala.collection
import scala.collection.immutable.SortedSet
import scala.collection.mutable

// naive CNF translation and simple DPLL solver
trait Solving extends Logic {
  trait CNF extends PropositionalLogic {
    import scala.collection.mutable.ArrayBuffer
    type FormulaBuilder = ArrayBuffer[Clause]
    def formulaBuilder  = ArrayBuffer[Clause]()
    def formulaBuilderSized(init: Int)  = new ArrayBuffer[Clause](init)
    def addFormula(buff: FormulaBuilder, f: Formula): Unit = buff ++= f
    def toFormula(buff: FormulaBuilder): Formula = buff

    // CNF: a formula is a conjunction of clauses
    type Formula = FormulaBuilder
    def formula(c: Clause*): Formula = ArrayBuffer(c: _*)

    type Clause  = Set[Lit]

    // a clause is a disjunction of distinct literals
    def clause(l: Lit*): Clause = l.toSet

    /** Conjunctive normal form (of a Boolean formula).
     *  A formula in this form is amenable to a SAT solver
     *  (i.e., solver that decides satisfiability of a formula).
     */
    type Cnf = Array[Clause]

    case class Solvable(cnf: Cnf, symForVar: Map[Int, Sym])

//    type Lit
//    def Lit(sym: Sym, pos: Boolean = true): Lit

    def andFormula(a: Formula, b: Formula): Formula = a ++ b
    def simplifyFormula(a: Formula): Formula = a.distinct

    private def merge(a: Clause, b: Clause) = a ++ b

    object AnalysisBudget {
      val max = 256

      abstract class Exception extends RuntimeException("CNF budget exceeded")

      object exceeded extends Exception

    }


    def eqFreePropToSolvable(p: Prop, fail: Boolean = false): Solvable = {
      def negationNormalFormNot(p: Prop): Prop =
        p match {
          case And(ops) if ops.size == 2 =>
            val a = ops.head
            val b = ops.last
            Or(negationNormalFormNot(a), negationNormalFormNot(b))
          case And(ops) if ops.size == 1 =>
            val a = ops.head
            negationNormalFormNot(a)
          case And(ops)                  =>
            val hd :: tl = ops.toList
            Or(negationNormalFormNot(hd), negationNormalFormNot(And(tl: _*)))
          case Or(ops) if ops.size == 2  =>
            val a = ops.head
            val b = ops.last
            And(negationNormalFormNot(a), negationNormalFormNot(b))
          case Or(ops)                   =>
            val hd :: tl = ops.toList
            And(negationNormalFormNot(hd), negationNormalFormNot(Or(tl: _*)))
          case Not(p)                    => negationNormalForm(p)
          case True                      => False
          case False                     => True
          case s: Sym                    => Not(s)
        }

      def negationNormalForm(p: Prop): Prop = p match {
        case And(ops) if ops.size == 2 =>
          val a = ops.head
          val b = ops.last
          And(negationNormalForm(a), negationNormalForm(b))
        case And(ops) if ops.size == 1 =>
          val a = ops.head
          negationNormalForm(a)
        case And(ops) if ops.isEmpty =>
          println(s"WTF empty and")
          True
        case And(ops)                  =>
          val hd :: tl = ops.toList
          And(negationNormalForm(hd), negationNormalForm(And(tl: _*)))
        case Or(ops) if ops.size == 2  =>
          val a = ops.head
          val b = ops.last
          Or(negationNormalForm(a), negationNormalForm(b))
        case Or(ops) if ops.size == 1  =>
          val a = ops.head
          negationNormalForm(a)
        case Or(ops) if ops.isEmpty =>
          println(s"WTF empty or")
          False
        case Or(ops)                   =>
          val hd :: tl = ops.toList
          Or(negationNormalForm(hd), negationNormalForm(Or(tl: _*)))
        case Not(negated)              => negationNormalFormNot(negated)
        case True
             | False
             | (_: Sym)                => p
      }

      type Formula = mutable.ArrayBuffer[Clause]

      def formula(c: Clause*): Formula = ArrayBuffer(c.toSeq: _*)

      val TrueF = formula()
      val FalseF = formula(clause())

      val symbols = mutable.Map[Int, Sym]()

      def symForVar = symbols.toMap

      def lit(s: Sym) = {
        symbols += (s.id -> s)
        formula(clause(Lit(s.id)))
      }
      def negLit(s: Sym) = {
        symbols += (s.id -> s)
        formula(clause(-Lit(s.id)))
      }

      def merge(a: Clause, b: Clause) = a ++ b

      def conjunctiveNormalForm(p: Prop): Formula = {
        def distribute(a: Formula, b: Formula): Formula =
          (a, b) match {
            // true \/ _ = true
            // _ \/ true = true
            case (trueA, trueB) if trueA.size == 0 || trueB.size == 0 => TrueF
            // lit \/ lit
            case (a, b) if a.size == 1 && b.size == 1 => formula(merge(a(0), b(0)))
            // (c1 /\ ... /\ cn) \/ d = ((c1 \/ d) /\ ... /\ (cn \/ d))
            // d \/ (c1 /\ ... /\ cn) = ((d \/ c1) /\ ... /\ (d \/ cn))
            case (cs, ds) =>
              val (big, small) = if (cs.size > ds.size) (cs, ds) else (ds, cs)
              big flatMap (c => distribute(formula(c), small))
          }

        p match {
          case True                     => TrueF
          case False                    => FalseF
          case s: Sym                   => lit(s)
          case Not(s: Sym)              => negLit(s)
          case And(ops)                 =>
            formula(ops.map(conjunctiveNormalForm).flatten.toSeq: _*)
          case Or(ops) if ops.size == 2 =>
            val a = ops.head
            val b = ops.last
            val cnfA = conjunctiveNormalForm(a)
            val cnfB = conjunctiveNormalForm(b)
            distribute(cnfA, cnfB)
          case Or(ops) if ops.size == 1 =>
            val a = ops.head
            val cnfA = conjunctiveNormalForm(a)
            cnfA
          case Or(ops)                  =>
            val hd :: tl = ops.toList
            val cnfA = conjunctiveNormalForm(hd)
            val cnfB = conjunctiveNormalForm(Or(tl: _*))
            distribute(cnfA, cnfB)
        }
      }

      val res = conjunctiveNormalForm(negationNormalForm(p))
      Solvable(res.toArray, symForVar)
    }

    trait CnfBuilder {
      type Cache = Map[Sym, Lit]

      val cache = mutable.Map[Sym, Lit]()

      private[this] val buff = ArrayBuffer[Clause]()

      private[this] var literalCount = 0

      lazy val constTrue: Lit = {
        val constTrue = newLiteral()
        addClauseProcessed(clause(constTrue))
        constTrue
      }

      def constFalse: Lit = -constTrue

      def isConst(l: Lit): Boolean = l == constTrue || l == constFalse

      /**
       * @return new Tseitin variable
       */
      def newLiteral(): Lit = {
        literalCount += 1
        Lit(literalCount)
      }

      def convertSym(sym: Sym): Lit = {
        cache.getOrElse(sym, {
          val l = newLiteral()
          cache += (sym -> l)
          l
        })
      }

      def addClauseProcessed(clause: Clause) {
        if (clause.nonEmpty) {
          buff += clause
        }
      }

      def buildCnf: Array[Clause] = buff.toArray

      // all variables are guaranteed to be in cache
      // (doesn't mean they will appear in the resulting formula)
      def symForVar: Map[Int, Sym] = cache.collect {
        case (sym: Sym, lit) => lit.variable -> sym
      }(collection.breakOut) // breakOut in order to obtain immutable Map

    }

    /** Tseitin transformation: used for conversion of a
      * propositional formula into conjunctive normal form (CNF)
      * (input format for SAT solver).
      * A simple conversion into CNF via Shannon expansion would
      * also be possible but it's worst-case complexity is exponential
      * (in the number of variables) and thus even simple problems
      * could become untractable.
      * The Tseitin transformation results in an _equisatisfiable_
      * CNF-formula (it generates auxiliary variables)
      * but runs with linear complexity.
      */
    class Tseitin() extends CnfBuilder {
      val plaisted = true
      def apply(p: Prop): Solvable = {

        def convert(p: Prop): Lit = {
          p match {
            case And(fv)  =>
              and(fv.map(convert))
            case Or(fv)   =>
              or(fv.map(convert))
            case Not(a)   =>
              not(convert(a))
            case sym: Sym =>
              convertSym(sym)
            case True     =>
              constTrue
            case False    =>
              constFalse
            case _: Eq    =>
              throw new MatchError(p)
          }
        }

        def and(bv: Set[Lit]): Lit = {
          if (bv.isEmpty) {
            // this case can actually happen because `removeVarEq` could add no constraints
            constTrue
          } else if (bv.size == 1) {
            bv.head
          } else if (bv.contains(constFalse)) {
            constFalse
          } else {
            // op1*op2*...*opx <==> (op1 + o')(op2 + o')... (opx + o')(op1' + op2' +... + opx' + o)
            val new_bv = bv - constTrue // ignore `True`
            val o = newLiteral() // auxiliary Tseitin variable
            if (!plaisted) new_bv.map(op => addClauseProcessed(clause(op, -o)))
            addClauseProcessed(new_bv.map(op => -op) + o)
            o
          }
        }

        def or(bv: Set[Lit]): Lit = {
          if (bv.isEmpty) {
            constFalse
          } else if (bv.size == 1) {
            bv.head
          } else if (bv.contains(constTrue)) {
            constTrue
          } else {
            // op1+op2+...+opx <==> (op1' + o)(op2' + o)... (opx' + o)(op1 + op2 +... + opx + o')
            val new_bv = bv - constFalse // ignore `False`
            val o = newLiteral() // auxiliary Tseitin variable
            if (!plaisted) new_bv.map(op => addClauseProcessed(clause(-op, o)))
            addClauseProcessed(new_bv + (-o))
            o
          }
        }

        // no need for auxiliary variable
        def not(a: Lit): Lit = -a

        // add intermediate variable since we want the formula to be SAT!
        addClauseProcessed(clause(convert(p)))

        def cnfString(f: Array[Clause]): String = {
          // TODO: fixme
          val lits: Array[List[String]] = f map (_.map(_.toString).toList)
          val xss: List[List[String]] = lits toList
          val a: String = alignAcrossRows(xss, "\\/", " /\\\n")
          a
        }

        println("#clauses: " + buildCnf.size)
        println(cnfString(buildCnf))
        Solvable(buildCnf, symForVar)
      }
    }

    class AlreadyInCNF {

      val symbols = mutable.Map[Int, Sym]()

      private def symForVar = symbols.toMap

      object ToLiteral {
        def unapply(f: Prop): Option[Lit] = f match {
          case Not(ToLiteral(lit)) => Some(-lit)
          case sym: Sym            =>
            symbols += (sym.id -> sym)
            Some(Lit(sym.id))
          case _                   => None
        }
      }

      object ToDisjunction {
        def unapply(f: Prop): Option[Array[Clause]] = f match {
          case Or(fv)         =>
            val cl = fv.foldLeft(Option(clause())) {
              case (Some(clause), ToLiteral(lit)) =>
                Some(clause + lit)
              case (_, _)                         =>
                None
            }
            cl.map(Array(_))
          case True           => Some(Array()) // empty, no clauses needed
          case False          => Some(Array(clause())) // empty clause can't be satisfied
          case ToLiteral(lit) => Some(Array(clause(lit)))
          case _              => None
        }
      }

      /**
       * Checks if propositional formula is already in CNF
       */
      object ToCnf {
        def unapply(f: Prop): Option[Solvable] = f match {
          case ToDisjunction(clauses) => Some(Solvable(clauses, symForVar) )
          case And(fv)                =>
            val clauses = fv.foldLeft(Option(mutable.ArrayBuffer[Clause]())) {
              case (Some(cnf), ToDisjunction(clauses)) =>
                Some(cnf ++= clauses)
              case (_, _)                              =>
                None
            }
            clauses.map(c => Solvable(c.toArray, symForVar))
          case _                      => None
        }
      }
    }

    def eqFreePropToSolvableTseitin(p: Prop): Solvable = {
      //      // we must take all vars from non simplified formula
      //      // otherwise if we get `T` as formula, we don't expand the variables
      //      // that are not in the formula...
      //      val allVars = {
      //        val vars: Set[Var] = gatherVariables(p)
      //
      //        val vars = mutable.Set[Int]()
      //        for {
      //          clause <- solvable.cnf
      //          lit <- clause
      //        } {
      //          vars += lit.variable
      //        }
      //        vars
      //      }

      val simplified = simplify(p)
      val cnfExtractor = new AlreadyInCNF
      simplified match {
        case cnfExtractor.ToCnf(clauses) =>
          println("already CNF...")
          // this is needed because t6942 would generate too many clauses with Tseitin
          // already in CNF, just add clauses
          clauses
        case p                           =>
          println("tseitin...")
          new Tseitin().apply(p)
      }
    }
  }

  // simple solver using DPLL
  trait Solver extends CNF {
    // a literal is a (possibly negated) variable

    // adapted from http://lara.epfl.ch/w/sav10:simple_sat_solver (original by Hossein Hojjat)
    val EmptyModel = collection.immutable.SortedMap.empty[Sym, Boolean]
    val NoModel: Model = null

    def formatModels(models: List[Model]) = {
      val groupedByKey = models.groupBy {
        model => model.keySet
      }.mapValues {
        models =>
          models.sortWith {
            case (a, b) =>
            val keys = a.keys
            val decider = keys.dropWhile(key => a(key) == b(key))
            decider.headOption.map(key => a(key) < b(key)).getOrElse(false)
          }
      }

      val sortedByKeys: Seq[(Set[Sym], List[Model])] = groupedByKey.toSeq.sortBy {
        case (syms, models) => syms.map(_.id).toIterable
      }

      (for {
        (keys, models: List[Model]) <- sortedByKeys
        model <- models
      } yield {
        (for {
          (sym, value) <- model
        } yield {
          s"""$sym = ${if (value) "T" else "F"}"""
        }).mkString(", ")
      }).mkString("\n")
    }

    def formatModels0(models: List[TseitinModel]) = {
      (for {
        model: Seq[Lit] <- models.map(_.toSeq.sorted)
      } yield {
        model.mkString(", ")
      }).mkString("\n")
    }

    // returns all solutions, if any (TODO: better infinite recursion backstop -- detect fixpoint??)
    def findAllModelsFor(solvable: Solvable): List[Model] = {
//      println(s"""findAllModelsFor ${solvable.cnf.clauses.mkString(", ")}""")
//      debug.patmat("find all models for\n"+ cnfString(f))

      val syms: Set[Sym] = solvable.symForVar.values.toSet
      val vars: Set[Int] = solvable.symForVar.keySet
      val ord: Map[Sym, Int] = syms.toSeq.reverse.zipWithIndex.toMap

      val CompatibleOrdering = Ordering.by[Int, Int] {
        variable =>
          val symOpt: Int = solvable.symForVar.get(variable).map(ord).getOrElse(-variable) // negative to be ordered after
          symOpt
      }

//      val allVars = {
//        val vars = mutable.Set[Int]()
//        for {
//          clause <- solvable.cnf
//          lit <- clause
//        } {
//          vars += lit.variable
//        }
//        vars
//      }

      val relevantVars: Set[Int] = solvable.symForVar.keySet.map(math.abs)
      val allVars = relevantVars

      // debug.patmat("vars "+ vars)
      // the negation of a model -(S1=True/False /\ ... /\ SN=True/False) = clause(S1=False/True, ...., SN=False/True)
      // (i.e. the blocking clause - used for ALL-SAT)
      def negateModel(m: TseitinModel) = {
        // filter out auxiliary Tseitin variables
        val relevantLits = m.filter(l => relevantVars.contains(l.variable))
        relevantLits.map(lit => -lit)
        m.map(lit => -lit)
      }

      /**
       * The DPLL procedure only returns a minimal mapping from literal to value
       * such that the CNF formula is satisfied.
       * E.g. for:
       * `(a \/ b)`
       * The DPLL procedure will find either {a = true} or {b = true}
       * as solution.
       *
       * The expansion step will amend both solutions with the unassigned variable
       * i.e., {a = true} will be expanded to {a = true, b = true} and {a = true, b = false}.
       */
      def expandUnassigned(unassigned: List[Int], model: TseitinModel): List[TseitinModel] = {
        // the number of solutions is doubled for every unassigned variable
        val expandedModels = 1 << unassigned.size
        var current = mutable.ArrayBuffer[TseitinModel]()
        var next = mutable.ArrayBuffer[TseitinModel]()
        current.sizeHint(expandedModels)
        next.sizeHint(expandedModels)

        current += model

        // we use double buffering:
        // read from `current` and create a two models for each model in `next`
        for {
          s <- unassigned
        } {
          for {
            model <- current
          } {
            def force(l: Lit) = model + l

            next += force(Lit(s))
            next += force(Lit(-s))
          }

          val tmp = current
          current = next
          next = tmp

          next.clear()
        }

        current.toList
      }

      def findAllModels(clauses: Array[Clause],
                        models: List[TseitinModel],
      recursionDepthAllowed: Int = Integer.MAX_VALUE): List[TseitinModel]=
        if (recursionDepthAllowed == 0) {
          models
        } else {
          val model = findTseitinModelFor(clauses, relevantVars)
          // if we found a solution, conjunct the formula with the model's negation and recurse
          if (model ne NoTseitinModel) {
            val unassigned: List[Int] = (allVars -- model.map(lit => lit.variable)).toList

//          debug.patmat("unassigned "+ unassigned +" in "+ model)
            // TODO: will crash for direct CNF

            val forced = expandUnassigned(unassigned, model)
            val negated = negateModel(model)
            findAllModels(clauses :+ negated, forced ++ models, recursionDepthAllowed - 1)
          }
          else models
        }

      val tseitinModels: List[TseitinModel] = findAllModels(solvable.cnf, Nil)
      println(formatModels0(tseitinModels))
      val models: List[Model] = tseitinModels.map(projectToModel(_, solvable.symForVar))

      val grouped: Seq[(Set[Sym], List[Model])] = models.groupBy {
        model => model.keySet
      }.toSeq

      val sorted: Seq[(Set[Sym], List[Model])] = grouped.sortBy {
        case (syms, models) => syms.map(_.id).toIterable
      }

//      for {
//        (keys, models) <- sorted
//        model <- models
//      } {
//        println(model)
//      }

      models
    }

    private def withLit(res: TseitinModel, l: Lit): TseitinModel = {
      if (res eq NoTseitinModel) NoTseitinModel else res + l
    }

    /** Drop trivially true clauses, simplify others by dropping negation of `unitLit`.
     *
     *  Disjunctions that contain the literal we're making true in the returned model are trivially true.
     *  Clauses can be simplified by dropping the negation of the literal we're making true
     *  (since False \/ X == X)
     */
    private def dropUnit(clauses: Array[Clause], unitLit: Lit): Array[Clause] = {
      val negated = -unitLit
      val simplified = new mutable.ArrayBuffer[Clause](clauses.size)
      clauses foreach {
        case trivial if trivial contains unitLit => // drop
        case clause                              => simplified += clause - negated
      }
      simplified.toArray
    }

    def findModelFor(solvable: Solvable): Model = {
      //      println("findModelFor")
      val relevantVars: Set[Int] = solvable.symForVar.keySet.map(math.abs)
      projectToModel(findTseitinModelFor(solvable.cnf, relevantVars), solvable.symForVar)
    }

    def findTseitinModelFor(clauses: Array[Clause],
                            relevantVars: Set[Int]): TseitinModel = {
      @inline def orElse(a: TseitinModel, b: => TseitinModel) = if (a ne NoTseitinModel) a else b

//      if (reachedTime(stoppingNanos)) throw AnalysisBudget.timeout

//      debug.patmat(s"DPLL\n${cnfString(clauses)}")


      val unitClauses: Array[Clause] = clauses.filter(_.size == 1).sortWith {
        case (a, b) if relevantVars.contains(a.head.variable) == relevantVars.contains(b.head.variable) =>
          a.head.dimacs < b.head.dimacs
        case (a, b) =>
          relevantVars.contains(a.head.variable)
      }

      val satisfiableWithModel: TseitinModel =
        if (clauses isEmpty) EmptyTseitinModel
        else if (clauses exists (_.isEmpty)) NoTseitinModel
        else unitClauses.headOption match {
          case Some(unitClause) =>
            val unitLit = unitClause.head
            withLit(findTseitinModelFor(dropUnit(clauses, unitLit), relevantVars), unitLit)
          case _ =>
            // partition symbols according to whether they appear in positive and/or negative literals
            val pos = new mutable.HashSet[Int]()
            val neg = new mutable.HashSet[Int]()
            mforeach(clauses)(lit => if (lit.positive) pos += lit.variable else neg += lit.variable)

//            println(s"""pos ${pos.mkString(", ")}""")
//            println(s"""neg ${neg.mkString(", ")}""")

            // appearing in both positive and negative
            val impures = pos intersect neg
            // appearing only in either positive/negative positions
            val pures = (pos ++ neg) -- impures
            val (relevantPures, nonRelevantPures) = pures.partition(relevantVars.contains)

            if (relevantPures nonEmpty) {
              val pureVar = relevantPures.head
              // turn it back into a literal
              // (since equality on literals is in terms of equality
              //  of the underlying symbol and its positivity, simply construct a new Lit)
              val pureLit = Lit(if (neg(pureVar)) -pureVar else pureVar)
              // debug.patmat("pure: "+ pureLit +" pures: "+ pures +" impures: "+ impures)
              val simplified = clauses.filterNot(_.contains(pureLit))
              withLit(findTseitinModelFor(simplified, relevantVars), pureLit)
            } else {
              val relevantSplit = clauses.flatMap {
                cl => cl.filter(lit => relevantVars.contains(lit.variable))
              }.headOption

              if(relevantSplit.isEmpty) {
                println("asdasd")
              }

              val split = if(relevantSplit.nonEmpty) relevantSplit.head else clauses.head.head

              // debug.patmat("split: "+ split)
              orElse(findTseitinModelFor(clauses :+ clause(split), relevantVars),
                findTseitinModelFor(clauses :+ clause(-split), relevantVars))
            }
        }

      satisfiableWithModel
    }

    private def projectToModel(model: TseitinModel, symForVar: Map[Int, Sym]): Model =
      if (model == NoTseitinModel) NoModel
      else {
        object SymForVar {
          def unapply(lit: Lit): Option[Sym] = {
            symForVar.get(lit.variable)
          }
        }
//        val b: List[(Sym, Boolean)] = model.toList collect {
//          case SymForVar(sym) => (sym, lit.positive)
//        }
        val a: List[(Sym, Boolean)] = model.toList collect {
          case lit if symForVar isDefinedAt lit.variable => (symForVar(lit.variable), lit.positive)
        }
        if(a.isEmpty) {
          println(s"empty projection...")
          NoModel
        } else {
          collection.immutable.SortedMap(a: _*)
        }
      }

  }

}
