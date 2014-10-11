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

    type Clause  = collection.Set[Lit]
    // a clause is a disjunction of distinct literals
    def clause(l: Lit*): Clause = (
      if (l.lengthCompare(1) <= 0) {
        l.toSet // SI-8531 Avoid LinkedHashSet's bulk for 0 and 1 element clauses
      } else {
        // neg/t7020.scala changes output 1% of the time, the non-determinism is quelled with this linked set
        mutable.LinkedHashSet(l: _*)
      }
    )

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
      def clause(l: Lit*): Clause = l.toSet

      val TrueF = formula()
      val FalseF = formula(clause())
      val cnf = new CNFBuilder
      val cache = mutable.Map[Sym, Lit]()
      def lit(s: Sym) = {
        if (!cache.contains(s)) {
          cache += s -> cnf.newLiteral()
        }
        formula(clause(cache(s)))
      }
      def negLit(s: Sym) = {
        if (!cache.contains(s)) {
          cache += s -> cnf.newLiteral()
        }
        formula(clause(-cache(s)))
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
      val res   = conjunctiveNormalForm(negationNormalForm(p))
      res.map(cnf.addClauseRaw)

      // all variables are guaranteed to be in cache
      // (doesn't mean they will appear in the resulting formula)
      val symForVar: Map[Int, Sym] = cache.collect {
        case (sym: Sym, lit) => lit.variable -> sym
      }(collection.breakOut) // breakOut in order to obtain immutable Map

      Solvable(cnf, symForVar)
    }

    def eqFreePropToSolvableTseitin(p: Prop): Solvable = {
      type Cache = Map[Prop, Lit]

      val cache = mutable.Map[Prop, Lit]()

      val cnf = new CNFBuilder

      def convertWithoutCache(p: Prop): Lit = {
        p match {
          case And(fv) =>
            and(fv.map(convertWithCache))
          case Or(fv)  =>
            or(fv.map(convertWithCache))
          case Not(a)  =>
            not(convertWithCache(a))
          case _: Sym  =>
            val l = cnf.newLiteral()
                        println(s"created $l for $p")
            l
          case True    =>
            cnf.constTrue
          case False   =>
            cnf.constFalse
          case _: Eq   =>
//            debug.patmat("Forgot to call propToSolvable()?")
            throw new MatchError(p)
        }
      }

      def convertWithCache(p: Prop): Lit = {
        cache.getOrElse(p, {
          val l = convertWithoutCache(p)
          require(!cache.isDefinedAt(p), "loop in formula?")
          println(s"added $p -> $l")
          cache += (p -> l)
          l
        })
      }

      def and(bv: Set[Lit]): Lit = {
        import cnf._
        if (bv.isEmpty) {
          constTrue
        } else if (bv.size == 1) {
          bv.head
        } else if (bv.contains(constFalse)) {
          constFalse
        } else {
          // op1*op2*...*opx <==> (op1 + o')(op2 + o')... (opx + o')(op1' + op2' +... + opx' + o)
          val new_bv = bv - constTrue // ignore `True`
          val o = newLiteral() // auxiliary Tseitin variable
          new_bv.map(op => addClauseProcessed(op, -o))
          addClauseProcessed((new_bv.map(op => -op) + o).toSeq: _*)
          o
        }
      }

      def or(bv: Set[Lit]): Lit = {
        import cnf._
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
          new_bv.map(op => addClauseProcessed(-op, o))
          addClauseProcessed((new_bv + (-o)).toSeq: _*)
          o
        }
      }

      // no need for auxiliary variable
      def not(a: Lit): Lit = -a

      def toLiteral(f: Prop): Option[Lit] = f match {
        case Not(a)   =>
          toLiteral(a).map(lit => -lit)
        case sym: Sym =>
          //          Some(convertWithCache(f)) // go via cache in order to get single literal for variable

          val l: Lit = Lit(sym.id)
          cache += (sym -> l)
          Some(l) // keep variable number to get compatible ordering
        case True     =>
          Some(cnf.constTrue)
        case False    =>
          Some(cnf.constFalse)
        case _        =>
          None
      }

      object ToDisjunction {
        def unapply(f: Prop): Option[Clause] = f match {
          case Or(fv) =>
            val a: Option[Clause] = fv.foldLeft(Option(Set[Lit]())) {
              case (Some(clause), p) =>
                toLiteral(p).map(clause + _)
              case (_, _)            =>
                None
            }
            a
          case p      =>
            toLiteral(p).map(Set(_))
        }
      }

      /**
       * Checks if propositional formula is already in CNF
       */
      object ToCnf {
        def unapply(f: Prop): Option[mutable.ArrayBuffer[Clause]] = f match {
          case And(fv) =>
            fv.foldLeft(Option(mutable.ArrayBuffer[Clause]())) {
              case (Some(cnf), ToDisjunction(clause)) =>
                Some(cnf += clause)
              case (_, _)                             =>
                None
            }
          //          case True    =>
          //            Some(cnf.constTrue)
          //          case False   =>
          //            Some(cnf.constFalse)
          case p =>
            ToDisjunction.unapply(p).map(mutable.ArrayBuffer[Clause](_))
        }
      }

      val simplified: Prop = simplify(p)
      simplified match {
        case ToCnf(clauses) =>
          println("already in CNF")
          // already in CNF, just add clauses
          clauses.foreach(clause => cnf.addClauseRaw(clause))
        case p              =>
          cache.clear() // side-effects!!! literal could already be there!
          println("convert to CNF")
          // add intermediate variable since we want the formula to be SAT!
          cnf.addClauseProcessed(convertWithCache(p))
      }

      // all variables are guaranteed to be in cache
      // (doesn't mean they will appear in the resulting formula)
      val symForVar: Map[Int, Sym] = cache.collect {
        case (sym: Sym, lit) => lit.variable -> sym
      }(collection.breakOut) // breakOut in order to obtain immutable Map

      Solvable(cnf, symForVar)
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

      val allVars: Set[Int] = solvable.cnf.allVariables

      // debug.patmat("vars "+ vars)
      // the negation of a model -(S1=True/False /\ ... /\ SN=True/False) = clause(S1=False/True, ...., SN=False/True)
      // (i.e. the blocking clause - used for ALL-SAT)
      def negateModel(m: TseitinModel) = m.map(lit => -lit)

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
          val model = findTseitinModelFor(clauses)
          // if we found a solution, conjunct the formula with the model's negation and recurse
          if (model ne NoTseitinModel) {
            val unassigned0: List[Int] = (allVars -- model.map(lit => lit.variable)).toList
            val unassigned = unassigned0.sorted(CompatibleOrdering)
//          debug.patmat("unassigned "+ unassigned +" in "+ model)
            // TODO: will crash for direct CNF

            val forced = expandUnassigned(unassigned, model)
            val negated = negateModel(model)
            findAllModels(clauses :+ negated, forced ++ models, recursionDepthAllowed - 1)
          }
          else models
        }

      val tseitinModels: List[TseitinModel] = findAllModels(solvable.cnf.clauses, Nil)
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
      projectToModel(findTseitinModelFor(solvable.cnf.clauses), solvable.symForVar)
    }

    def findTseitinModelFor(clauses: Array[Clause]): TseitinModel = {
      @inline def orElse(a: TseitinModel, b: => TseitinModel) = if (a ne NoTseitinModel) a else b

//      if (reachedTime(stoppingNanos)) throw AnalysisBudget.timeout

//      debug.patmat(s"DPLL\n${cnfString(clauses)}")

      val satisfiableWithModel: TseitinModel =
        if (clauses isEmpty) EmptyTseitinModel
        else if (clauses exists (_.isEmpty)) NoTseitinModel
        else clauses.find(_.size == 1) match {
          case Some(unitClause) =>
            val unitLit = unitClause.head
            withLit(findTseitinModelFor(dropUnit(clauses, unitLit)), unitLit)
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

            if (pures nonEmpty) {
              val pureVar = pures.head
              // turn it back into a literal
              // (since equality on literals is in terms of equality
              //  of the underlying symbol and its positivity, simply construct a new Lit)
              val pureLit = Lit(if (neg(pureVar)) -pureVar else pureVar)
              // debug.patmat("pure: "+ pureLit +" pures: "+ pures +" impures: "+ impures)
              val simplified = clauses.filterNot(_.contains(pureLit))
              withLit(findTseitinModelFor(simplified), pureLit)
            } else {
              val split = clauses.head.head
              // debug.patmat("split: "+ split)
              orElse(findTseitinModelFor(clauses :+ clause(split)), findTseitinModelFor(clauses :+ clause(-split)))
            }
        }

      satisfiableWithModel
    }

    private def projectToModel(model: TseitinModel, symForVar: Map[Int, Sym]): Model =
      if (model == NoTseitinModel) NoModel
      else {
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
