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
}
