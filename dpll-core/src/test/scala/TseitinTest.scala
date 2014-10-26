import org.scalacheck.{Prop, Arbitrary, Gen}

/**
 * Tests:
 *
 * - random formula, equisat: formula / simplified formula
 * - random formula, equisat: tseitin / plaisted: not possible since XOR would enforce both polarities
 * thus resulting in exactly the same formula
 * - random formula, less models tseitin / plaisted, distinct: same models
 *
 * TODO:
 * - what happens with Sym that is not translated? trivially true?
 * - sharing of subformulae!
 */
class TseitinTest extends BaseSpecification {

  object Outer extends Solving {

    object Aggregate extends Solver {

      def allTseitinModels(f: Prop): List[Model] = {
        findAllModelsFor(eqFreePropToSolvableTseitin(f))
      }

      def allPlaistedModels(f: Prop): List[Model] = {
        findAllModelsFor(eqFreePropToSolvableTseitin(f, true))
      }

      def equiModels(f: Prop) = {
        val tseitinModels = allTseitinModels(f)

        val plaistedModels = allPlaistedModels(f)

        tseitinModels.length must be_<=(plaistedModels.length)
        formatModels(tseitinModels) === formatModels(plaistedModels)
      }

      def checkModels(a: Seq[Model], b: Seq[Model]) = {
        a.length must be_==(b.length)
        for {
          ma <- a
        } yield {
          ma must beLike {
            case (m: Model) if b.contains(m) => ok
          }
        }
      }

      def stringsForModels(models: Seq[Model]): Seq[String] = {
        for {
          m <- models
        } yield {
          val s = for {
            (v, a) <- m
          } yield {
            s"${v.variable}=${if (a) "1" else "0"}"
          }
          s"model ${s.mkString(", ")}"
        }
      }

      def testP = {
        val f = Sym("p")
        val models = allTseitinModels(f)
        models must be_==(Seq(Map(Sym("p") -> true)))
      }

      def testNotP = {
        val f = Not(Sym("p"))
        val models = allTseitinModels(f)
        models must be_==(Seq(Map(Sym("p") -> false)))
      }

      def pOrQ = {
        val f = Or(Sym("p"), Sym("q"))
        val models = allTseitinModels(f)
        //      println(stringsForModels(models).mkString("\n"))
        checkModels(models, Seq(
          Map(Sym("p") -> false, Sym("q") -> true),
          Map(Sym("p") -> true, Sym("q") -> false),
          Map(Sym("p") -> true, Sym("q") -> true)
        ))

        //          "equi models for Tseitin & Plaisted" in {
        //            equiModels(f)
        //          }
      }

      def notPorQ = {
        val f = Not(Or(Sym("p"), Sym("q")))
        val models = allTseitinModels(f)
        //      println(stringsForModels(models).mkString("\n"))
        checkModels(models, Seq(
          Map(Sym("p") -> false, Sym("q") -> false)
        ))
      }

      def pOrNotp = {
        val f = Or(Sym("p"), Not(Sym("p")))
        val models = allTseitinModels(f)
        //      println(stringsForModels(models).mkString("\n"))
        checkModels(models, Seq(
          Map(Sym("p") -> false),
          Map(Sym("p") -> true)
        ))
      }

      def complicated = {
        val f = Or(And(Sym("a"), Not(Sym("b"))), And(Sym("c"), Not(Sym("d")), Sym("e")))
        equiModels(f)
      }

      def scalacFormula = {
        def Sym(name: String, index: Int) = new Sym(name)

        val formula = Or(Or(Or(Or(Or(Or(Or(Or(Or(Or(Or(Or(Or(Or(Or(Or(Or(Or(Or(Sym("V1=Z0", 1), And(And(Not(Sym("V1=null", 2)), Sym("V1=Z.Z1", 3)), Not(Sym("V1=null", 2)))), Sym("V1=Z2", 4)), And(And(Not(Sym("V1=null", 2)), Sym("V1=Z.Z3", 5)), Not(Sym("V1=null", 2)))), Sym("V1=Z4", 6)), And(And(Not(Sym("V1=null", 2)), Sym("V1=Z.Z5", 7)), Not(Sym("V1=null", 2)))), Sym("V1=Z6", 8)), And(And(Not(Sym("V1=null", 2)), Sym("V1=Z.Z7", 9)), Not(Sym("V1=null", 2)))), Sym("V1=Z8", 10)), And(And(Not(Sym("V1=null", 2)), Sym("V1=Z.Z9", 11)), Not(Sym("V1=null", 2)))), Sym("V1=Z10", 12)), And(And(Not(Sym("V1=null", 2)), Sym("V1=Z.Z11", 13)), Not(Sym("V1=null", 2)))), Sym("V1=Z12", 14)), And(And(Not(Sym("V1=null", 2)), Sym("V1=Z.Z13", 15)), Not(Sym("V1=null", 2)))), Sym("V1=Z14", 16)), And(And(Not(Sym("V1=null", 2)), Sym("V1=Z.Z15", 17)), Not(Sym("V1=null", 2)))), Sym("V1=Z16", 18)), And(And(Not(Sym("V1=null", 2)), Sym("V1=Z.Z17", 19)), Not(Sym("V1=null", 2)))), Sym("V1=Z18", 20)), And(And(Not(Sym("V1=null", 2)), Sym("V1=Z.Z19", 21)), Not(Sym("V1=null", 2))))
        equiModels(formula)
      }
    }

  }

  "simple examples" should {
    "p" in {
      Outer.Aggregate.testP
    }

    "!p" in {
      Outer.Aggregate.testNotP
    }

    "p + q" in {
      Outer.Aggregate.pOrQ
    }

    "!(p + q)" in {
      Outer.Aggregate.notPorQ
    }

    "p +!p" in {
      Outer.Aggregate.pOrNotp
    }

    "(a & ~b) | (c & ~d & e)" in {
      Outer.Aggregate.complicated
    }

    "scalac formula" in {
      skipped("hangs")
      Outer.Aggregate.scalacFormula
    }
  }

}
