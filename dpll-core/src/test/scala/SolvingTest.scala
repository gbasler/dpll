

class SolvingTest extends BaseSpecification {

  object Outer extends Solving {

    object Aggregate extends Solver {

      def printModels(models: List[Model]) {
        println("models")
        for {
          m <- models
        } {
          println("*** model ***")
          println(modelToString(m))
        }
      }

      private def modelToString(model: Model): String = {
        val keys = model.keys.toSeq.sortBy(_.toString)
        val s = for {
          k <- keys
        } yield {
          s"${k} = ${model(k)}"
        }
        s.mkString("\n")
      }

      def test = {
        val f = Not(Or(Or(Or(Or(And(And(And(And(True, Sym("Eq(V1, scala.collection.immutable.::[?])")), True), Sym("Eq(V2, 1)")), Sym("Eq(V3, Nil)")), And(And(And(And(True, Sym("Eq(V1, scala.collection.immutable.::[?])")), True), Sym("Eq(V2, 2)")), Sym("Eq(V3, Nil)"))), And(And(And(And(True, Sym("Eq(V1, scala.collection.immutable.::[?])")), True), Or(Or(Sym("Eq(V2, 4)"), Sym("Eq(V2, 5)")), Sym("Eq(V2, 6)"))), Sym("Eq(V3, Nil)"))), And(And(And(And(True, Sym("Eq(V1, scala.collection.immutable.::[?])")), True), Sym("Eq(V2, 7)")), Sym("Eq(V3, Nil)"))), Sym("Eq(V1, Nil)")))
        val s1 = findAllModelsFor(eqFreePropToSolvable(f))
        val s2 = findAllModelsFor(eqFreePropToSolvable(f))
        val s3 = findAllModelsFor(eqFreePropToSolvable(f))
        val s4 = findAllModelsFor(eqFreePropToSolvable(f))
        printModels(s4)
        ok
      }
    }

  }

  "4 formulae" in {
    Outer.Aggregate.test
  }

}
