class SolvingTest extends BaseSpecification {

  "small formula" in {
    object Outer extends Solving {

      object Aggregate extends Solver {

        def test = {
          val f = Not(Or(And(And(True, Sym("Eq(V2, 7)")), Sym("Eq(V3, Nil)")), Sym("Eq(V1, Nil)")))
          val s = findAllModelsFor(eqFreePropToSolvable(f))
          //          println(s" ${s.size} solutions")
          formatModels(s)
        }
      }

      object AggregateSat extends SatSolver {

        def test = {
          val f = Not(Or(And(And(True, Sym("Eq(V2, 7)")), Sym("Eq(V3, Nil)")), Sym("Eq(V1, Nil)")))
          val s = findAllModelsFor(eqFreePropToSolvable(f))
          //          println(s" ${s.size} solutions")
          formatModels(s)
        }
      }

    }
    Outer.Aggregate.test === Outer.AggregateSat.test
  }

  "bigger formula" in {
    object Outer extends Solving {

      object Aggregate extends Solver {

        def test = {
          val f = Not(Or(And(And(And(And(True, Sym("Eq(V1, scala.collection.immutable.::[?])")), True), Sym("Eq(V2, 7)")), Sym("Eq(V3, Nil)")), Sym("Eq(V1, Nil)")))
          val s = findAllModelsFor(eqFreePropToSolvable(f))
          formatModels(s)
        }
      }

      object AggregateSat extends SatSolver {

        def test = {
          val f = Not(Or(And(And(And(And(True, Sym("Eq(V1, scala.collection.immutable.::[?])")), True), Sym("Eq(V2, 7)")), Sym("Eq(V3, Nil)")), Sym("Eq(V1, Nil)")))
          val s = findAllModelsFor(eqFreePropToSolvable(f))
          formatModels(s)
        }
      }
    }
    Outer.Aggregate.test === Outer.AggregateSat.test
  }

  "huge formula" in {
    object Outer extends Solving {

      object Aggregate extends Solver {

        def test = {
          val f = Not(Or(Or(Or(Or(And(And(And(And(True, Sym("Eq(V1, scala.collection.immutable.::[?])")), True), Sym("Eq(V2, 1)")), Sym("Eq(V3, Nil)")), And(And(And(And(True, Sym("Eq(V1, scala.collection.immutable.::[?])")), True), Sym("Eq(V2, 2)")), Sym("Eq(V3, Nil)"))), And(And(And(And(True, Sym("Eq(V1, scala.collection.immutable.::[?])")), True), Or(Or(Sym("Eq(V2, 4)"), Sym("Eq(V2, 5)")), Sym("Eq(V2, 6)"))), Sym("Eq(V3, Nil)"))), And(And(And(And(True, Sym("Eq(V1, scala.collection.immutable.::[?])")), True), Sym("Eq(V2, 7)")), Sym("Eq(V3, Nil)"))), Sym("Eq(V1, Nil)")))
          val s = findAllModelsFor(eqFreePropToSolvable(f))
          formatModels(s)
        }
      }

      object AggregateSat extends SatSolver {

        def test = {
          val f = Not(Or(Or(Or(Or(And(And(And(And(True, Sym("Eq(V1, scala.collection.immutable.::[?])")), True), Sym("Eq(V2, 1)")), Sym("Eq(V3, Nil)")), And(And(And(And(True, Sym("Eq(V1, scala.collection.immutable.::[?])")), True), Sym("Eq(V2, 2)")), Sym("Eq(V3, Nil)"))), And(And(And(And(True, Sym("Eq(V1, scala.collection.immutable.::[?])")), True), Or(Or(Sym("Eq(V2, 4)"), Sym("Eq(V2, 5)")), Sym("Eq(V2, 6)"))), Sym("Eq(V3, Nil)"))), And(And(And(And(True, Sym("Eq(V1, scala.collection.immutable.::[?])")), True), Sym("Eq(V2, 7)")), Sym("Eq(V3, Nil)"))), Sym("Eq(V1, Nil)")))
          val s = findAllModelsFor(eqFreePropToSolvable(f))
          formatModels(s)
        }
      }
    }
    Outer.Aggregate.test === Outer.AggregateSat.test
  }

  "t8430 fixed" in {
    object Outer extends Solving {

      object Aggregate extends Solver {

        val clauses: Seq[Seq[Prop]] = {
          val c = Sym("V1=LetC.type#13")
          val f = Sym("V1=LetF.type#14")
          val l = Sym("V1=LetL#11")
          val p = Sym("V1=LetP.type#15")
          val boolLit = Sym("V2=BooleanLit.type#16")
          val charLit = Sym("V2=CharLit#12")
          val intLit = Sym("V2=IntLit.type#17")
          val unitLit = Sym("V2=UnitLit.type#18")

          Seq(
            Seq(c, f, l, p),
            Seq(Not(c), Not(f)),
            Seq(Not(c), Not(l)),
            Seq(Not(c), Not(p)),
            Seq(Not(f), Not(l)),
            Seq(Not(f), Not(p)),
            Seq(Not(l), Not(p)),
            Seq(boolLit, charLit, intLit, unitLit),
            Seq(Not(boolLit), Not(charLit)),
            Seq(Not(boolLit), Not(intLit)),
            Seq(Not(boolLit), Not(unitLit)),
            Seq(Not(charLit), Not(intLit)),
            Seq(Not(charLit), Not(unitLit)),
            Seq(Not(intLit), Not(unitLit)),
            Seq(Not(l), Not(charLit))
          )
        }

        val f: Seq[Prop] = for {
          clause: Seq[Prop] <- clauses
        } yield {
          clause.reduceLeft(Or)
        }
        val formula = f.reduceLeft(And)

        def test: String = {
          val s = findAllModelsFor(eqFreePropToSolvable(formula))
          formatModels(s)
        }
      }

      object AggregateSat extends SatSolver {

        def test = {
          val clauses: Seq[Seq[Prop]] = {
            val c = Sym("V1=LetC.type#13")
            val f = Sym("V1=LetF.type#14")
            val l = Sym("V1=LetL#11")
            val p = Sym("V1=LetP.type#15")
            val boolLit = Sym("V2=BooleanLit.type#16")
            val charLit = Sym("V2=CharLit#12")
            val intLit = Sym("V2=IntLit.type#17")
            val unitLit = Sym("V2=UnitLit.type#18")

            Seq(
              Seq(c, f, l, p),
              Seq(Not(c), Not(f)),
              Seq(Not(c), Not(l)),
              Seq(Not(c), Not(p)),
              Seq(Not(f), Not(l)),
              Seq(Not(f), Not(p)),
              Seq(Not(l), Not(p)),
              Seq(boolLit, charLit, intLit, unitLit),
              Seq(Not(boolLit), Not(charLit)),
              Seq(Not(boolLit), Not(intLit)),
              Seq(Not(boolLit), Not(unitLit)),
              Seq(Not(charLit), Not(intLit)),
              Seq(Not(charLit), Not(unitLit)),
              Seq(Not(intLit), Not(unitLit)),
              Seq(Not(l), Not(charLit))
            )
          }

          val f: Seq[Prop] = for {
            clause: Seq[Prop] <- clauses
          } yield {
            clause.reduceLeft(Or)
          }
          val formula = f.reduceLeft(And)
          val s = findAllModelsFor(eqFreePropToSolvable(formula))
          val res = formatModels(s)
          println(res)
          res
        }
      }

    }
    Outer.Aggregate.test === Outer.AggregateSat.test
  }
}
