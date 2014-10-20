import org.specs2.execute.Result

class SolvingTest extends BaseSpecification {

  "t7020" in {
    object Outer extends Solving {

      object Aggregate extends Solver {

        val formulas = Seq(
          And(And(And(Not(Sym("V1=null")), Sym("V1=scala.collection.immutable.::[?]")), And(Not(Sym("V1=null")), And(Or(Sym("V2=4"), Or(Sym("V2=5"), Sym("V2=6"))), Sym("V3=Nil")))), And(And(Or(Not(Sym("V1=scala.collection.immutable.::[?]")), Not(Sym("V1=null"))), And(Or(Sym("V3=scala.collection.immutable.::[?]"), Or(Sym("V3=Nil"), Sym("V3=null"))), And(Or(Not(Sym("V3=Nil")), Not(Sym("V3=null"))), And(Or(Not(Sym("V3=scala.collection.immutable.::[?]")), Not(Sym("V3=null"))), And(Or(Not(Sym("V1=Nil")), Not(Sym("V1=null"))), Or(Sym("V1=scala.collection.immutable.::[?]"), Or(Sym("V1=Nil"), Sym("V1=null")))))))), And(Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=1")), Not(Sym("V3=Nil"))))), Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=2")), Not(Sym("V3=Nil"))))))))
          , And(And(And(Not(Sym("V1=null")), Sym("V1=scala.collection.immutable.::[?]")), And(Not(Sym("V1=null")), And(Sym("V2=7"), Sym("V3=Nil")))), And(And(Or(Not(Sym("V1=scala.collection.immutable.::[?]")), Not(Sym("V1=null"))), And(Or(Sym("V3=scala.collection.immutable.::[?]"), Or(Sym("V3=Nil"), Sym("V3=null"))), And(Or(Not(Sym("V3=Nil")), Not(Sym("V3=null"))), And(Or(Not(Sym("V3=scala.collection.immutable.::[?]")), Not(Sym("V3=null"))), And(Or(Not(Sym("V1=Nil")), Not(Sym("V1=null"))), Or(Sym("V1=scala.collection.immutable.::[?]"), Or(Sym("V1=Nil"), Sym("V1=null")))))))), And(And(Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=1")), Not(Sym("V3=Nil"))))), Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=2")), Not(Sym("V3=Nil")))))), Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(And(Not(Sym("V2=4")), And(Not(Sym("V2=5")), Not(Sym("V2=6")))), Not(Sym("V3=Nil"))))))))
          , And(And(Not(Sym("V1=null")), Sym("V1=scala.collection.immutable.::[?]")), And(Not(Sym("V1=null")), And(Or(Sym("V2=4"), Or(Sym("V2=5"), Sym("V2=6"))), Sym("V3=Nil"))))
          , And(And(Not(Sym("V1=null")), Sym("V1=scala.collection.immutable.::[?]")), And(Not(Sym("V1=null")), And(Sym("V2=7"), Sym("V3=Nil"))))
          , And(And(Or(Not(Sym("V1=scala.collection.immutable.::[?]")), Not(Sym("V1=null"))), And(Or(Sym("V3=scala.collection.immutable.::[?]"), Or(Sym("V3=Nil"), Sym("V3=null"))), And(Or(Not(Sym("V3=Nil")), Not(Sym("V3=null"))), And(Or(Not(Sym("V3=scala.collection.immutable.::[?]")), Not(Sym("V3=null"))), And(Or(Not(Sym("V1=Nil")), Not(Sym("V1=null"))), Or(Sym("V1=scala.collection.immutable.::[?]"), Or(Sym("V1=Nil"), Sym("V1=null")))))))), And(And(Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=1")), Not(Sym("V3=Nil"))))), Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=2")), Not(Sym("V3=Nil")))))), Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(And(Not(Sym("V2=4")), And(Not(Sym("V2=5")), Not(Sym("V2=6")))), Not(Sym("V3=Nil")))))))
          , And(And(Or(Not(Sym("V1=scala.collection.immutable.::[?]")), Not(Sym("V1=null"))), And(Or(Sym("V3=scala.collection.immutable.::[?]"), Or(Sym("V3=Nil"), Sym("V3=null"))), And(Or(Not(Sym("V3=Nil")), Not(Sym("V3=null"))), And(Or(Not(Sym("V3=scala.collection.immutable.::[?]")), Not(Sym("V3=null"))), And(Or(Not(Sym("V1=Nil")), Not(Sym("V1=null"))), Or(Sym("V1=scala.collection.immutable.::[?]"), Or(Sym("V1=Nil"), Sym("V1=null")))))))), And(Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=1")), Not(Sym("V3=Nil"))))), Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=2")), Not(Sym("V3=Nil")))))))
          , And(And(Or(Not(Sym("V1=scala.collection.immutable.::[?]")), Not(Sym("V1=null"))), And(Or(Sym("V3=scala.collection.immutable.::[?]"), Or(Sym("V3=Nil"), Sym("V3=null"))), And(Or(Not(Sym("V3=Nil")), Not(Sym("V3=null"))), And(Or(Not(Sym("V3=scala.collection.immutable.::[?]")), Not(Sym("V3=null"))), And(Or(Not(Sym("V1=Nil")), Not(Sym("V1=null"))), Or(Sym("V1=scala.collection.immutable.::[?]"), Or(Sym("V1=Nil"), Sym("V1=null")))))))), And(Sym("V1=Nil"), And(Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(And(Not(Sym("V2=4")), And(Not(Sym("V2=5")), Not(Sym("V2=6")))), Not(Sym("V3=Nil"))))), And(Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=1")), Not(Sym("V3=Nil"))))), Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=2")), Not(Sym("V3=Nil")))))))))
          , And(And(Or(Or(False, Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(False, Or(Not(Sym("V2=1")), Not(Sym("V3=Nil"))))), Or(Or(False, Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(False, Or(Not(Sym("V2=2")), Not(Sym("V3=Nil")))))), And(Or(Or(False, Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(False, Or(And(Not(Sym("V2=4")), And(Not(Sym("V2=5")), Not(Sym("V2=6")))), Not(Sym("V3=Nil"))))), And(Or(Or(False, Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(False, Or(Not(Sym("V2=7")), Not(Sym("V3=Nil"))))), Not(Sym("V1=Nil")))))
          , And(And(Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=1")), Not(Sym("V3=Nil"))))), Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=2")), Not(Sym("V3=Nil")))))), Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(And(Not(Sym("V2=4")), And(Not(Sym("V2=5")), Not(Sym("V2=6")))), Not(Sym("V3=Nil"))))))
          , And(And(Or(Sym("V3=scala.collection.immutable.::[?]"), Sym("V3=Nil")), Or(Sym("V1=scala.collection.immutable.::[?]"), Sym("V1=Nil"))), And(And(Or(Or(False, Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(False, Or(Not(Sym("V2=1")), Not(Sym("V3=Nil"))))), Or(Or(False, Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(False, Or(Not(Sym("V2=2")), Not(Sym("V3=Nil")))))), And(Or(Or(False, Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(False, Or(And(Not(Sym("V2=4")), And(Not(Sym("V2=5")), Not(Sym("V2=6")))), Not(Sym("V3=Nil"))))), And(Or(Or(False, Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(False, Or(Not(Sym("V2=7")), Not(Sym("V3=Nil"))))), Not(Sym("V1=Nil"))))))
          , And(Not(Sym("V1=null")), And(Or(Sym("V2=4"), Or(Sym("V2=5"), Sym("V2=6"))), Sym("V3=Nil")))
          , And(Not(Sym("V1=null")), And(Sym("V2=7"), Sym("V3=Nil")))
          , And(Not(Sym("V1=null")), Sym("V1=scala.collection.immutable.::[?]"))
          , And(Not(Sym("V2=4")), And(Not(Sym("V2=5")), Not(Sym("V2=6"))))
          , And(Not(Sym("V2=5")), Not(Sym("V2=6")))
          , And(Or(Not(Sym("V1=Nil")), Not(Sym("V1=null"))), Or(Sym("V1=scala.collection.immutable.::[?]"), Or(Sym("V1=Nil"), Sym("V1=null"))))
          , And(Or(Not(Sym("V1=scala.collection.immutable.::[?]")), Not(Sym("V1=null"))), And(Or(Sym("V3=scala.collection.immutable.::[?]"), Or(Sym("V3=Nil"), Sym("V3=null"))), And(Or(Not(Sym("V3=Nil")), Not(Sym("V3=null"))), And(Or(Not(Sym("V3=scala.collection.immutable.::[?]")), Not(Sym("V3=null"))), And(Or(Not(Sym("V1=Nil")), Not(Sym("V1=null"))), Or(Sym("V1=scala.collection.immutable.::[?]"), Or(Sym("V1=Nil"), Sym("V1=null"))))))))
          , And(Or(Not(Sym("V3=Nil")), Not(Sym("V3=null"))), And(Or(Not(Sym("V3=scala.collection.immutable.::[?]")), Not(Sym("V3=null"))), And(Or(Not(Sym("V1=Nil")), Not(Sym("V1=null"))), Or(Sym("V1=scala.collection.immutable.::[?]"), Or(Sym("V1=Nil"), Sym("V1=null"))))))
          , And(Or(Not(Sym("V3=scala.collection.immutable.::[?]")), Not(Sym("V3=null"))), And(Or(Not(Sym("V1=Nil")), Not(Sym("V1=null"))), Or(Sym("V1=scala.collection.immutable.::[?]"), Or(Sym("V1=Nil"), Sym("V1=null")))))
          , And(Or(Or(False, Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(False, Or(And(Not(Sym("V2=4")), And(Not(Sym("V2=5")), Not(Sym("V2=6")))), Not(Sym("V3=Nil"))))), And(Or(Or(False, Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(False, Or(Not(Sym("V2=7")), Not(Sym("V3=Nil"))))), Not(Sym("V1=Nil"))))
          , And(Or(Or(False, Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(False, Or(Not(Sym("V2=1")), Not(Sym("V3=Nil"))))), Or(Or(False, Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(False, Or(Not(Sym("V2=2")), Not(Sym("V3=Nil"))))))
          , And(Or(Or(False, Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(False, Or(Not(Sym("V2=7")), Not(Sym("V3=Nil"))))), Not(Sym("V1=Nil")))
          , And(Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(And(Not(Sym("V2=4")), And(Not(Sym("V2=5")), Not(Sym("V2=6")))), Not(Sym("V3=Nil"))))), And(Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=1")), Not(Sym("V3=Nil"))))), Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=2")), Not(Sym("V3=Nil")))))))
          , And(Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=1")), Not(Sym("V3=Nil"))))), Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=2")), Not(Sym("V3=Nil"))))))
          , And(Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=7")), Not(Sym("V3=Nil"))))), And(And(Or(Not(Sym("V1=scala.collection.immutable.::[?]")), Not(Sym("V1=null"))), And(Or(Sym("V3=scala.collection.immutable.::[?]"), Or(Sym("V3=Nil"), Sym("V3=null"))), And(Or(Not(Sym("V3=Nil")), Not(Sym("V3=null"))), And(Or(Not(Sym("V3=scala.collection.immutable.::[?]")), Not(Sym("V3=null"))), And(Or(Not(Sym("V1=Nil")), Not(Sym("V1=null"))), Or(Sym("V1=scala.collection.immutable.::[?]"), Or(Sym("V1=Nil"), Sym("V1=null")))))))), And(Sym("V1=Nil"), And(Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(And(Not(Sym("V2=4")), And(Not(Sym("V2=5")), Not(Sym("V2=6")))), Not(Sym("V3=Nil"))))), And(Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=1")), Not(Sym("V3=Nil"))))), Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=2")), Not(Sym("V3=Nil"))))))))))
          , And(Or(Sym("V2=4"), Or(Sym("V2=5"), Sym("V2=6"))), Sym("V3=Nil"))
          , And(Or(Sym("V3=scala.collection.immutable.::[?]"), Or(Sym("V3=Nil"), Sym("V3=null"))), And(Or(Not(Sym("V3=Nil")), Not(Sym("V3=null"))), And(Or(Not(Sym("V3=scala.collection.immutable.::[?]")), Not(Sym("V3=null"))), And(Or(Not(Sym("V1=Nil")), Not(Sym("V1=null"))), Or(Sym("V1=scala.collection.immutable.::[?]"), Or(Sym("V1=Nil"), Sym("V1=null")))))))
          , And(Or(Sym("V3=scala.collection.immutable.::[?]"), Sym("V3=Nil")), Or(Sym("V1=scala.collection.immutable.::[?]"), Sym("V1=Nil")))
          , And(Sym("V1=Nil"), And(Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(And(Not(Sym("V2=4")), And(Not(Sym("V2=5")), Not(Sym("V2=6")))), Not(Sym("V3=Nil"))))), And(Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=1")), Not(Sym("V3=Nil"))))), Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=2")), Not(Sym("V3=Nil"))))))))
          , And(Sym("V2=7"), Sym("V3=Nil"))
          , False
          , Not(Sym("V1=Nil"))
          , Not(Sym("V1=null"))
          , Not(Sym("V1=scala.collection.immutable.::[?]"))
          , Not(Sym("V2=1"))
          , Not(Sym("V2=2"))
          , Not(Sym("V2=4"))
          , Not(Sym("V2=5"))
          , Not(Sym("V2=6"))
          , Not(Sym("V2=7"))
          , Not(Sym("V3=Nil"))
          , Not(Sym("V3=null"))
          , Not(Sym("V3=scala.collection.immutable.::[?]"))
          , Or(And(Not(Sym("V2=4")), And(Not(Sym("V2=5")), Not(Sym("V2=6")))), Not(Sym("V3=Nil")))
          , Or(False, Not(Sym("V1=scala.collection.immutable.::[?]")))
          , Or(False, Or(And(Not(Sym("V2=4")), And(Not(Sym("V2=5")), Not(Sym("V2=6")))), Not(Sym("V3=Nil"))))
          , Or(False, Or(Not(Sym("V2=1")), Not(Sym("V3=Nil"))))
          , Or(False, Or(Not(Sym("V2=2")), Not(Sym("V3=Nil"))))
          , Or(False, Or(Not(Sym("V2=7")), Not(Sym("V3=Nil"))))
          , Or(Not(Sym("V1=Nil")), Not(Sym("V1=null")))
          , Or(Not(Sym("V1=scala.collection.immutable.::[?]")), Not(Sym("V1=null")))
          , Or(Not(Sym("V2=1")), Not(Sym("V3=Nil")))
          , Or(Not(Sym("V2=2")), Not(Sym("V3=Nil")))
          , Or(Not(Sym("V2=7")), Not(Sym("V3=Nil")))
          , Or(Not(Sym("V3=Nil")), Not(Sym("V3=null")))
          , Or(Not(Sym("V3=scala.collection.immutable.::[?]")), Not(Sym("V3=null")))
          , Or(Or(False, Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(False, Or(And(Not(Sym("V2=4")), And(Not(Sym("V2=5")), Not(Sym("V2=6")))), Not(Sym("V3=Nil")))))
          , Or(Or(False, Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(False, Or(Not(Sym("V2=1")), Not(Sym("V3=Nil")))))
          , Or(Or(False, Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(False, Or(Not(Sym("V2=2")), Not(Sym("V3=Nil")))))
          , Or(Or(False, Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(False, Or(Not(Sym("V2=7")), Not(Sym("V3=Nil")))))
          , Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(And(Not(Sym("V2=4")), And(Not(Sym("V2=5")), Not(Sym("V2=6")))), Not(Sym("V3=Nil")))))
          , Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=1")), Not(Sym("V3=Nil")))))
          , Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=2")), Not(Sym("V3=Nil")))))
          , Or(Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]"))), Or(Sym("V1=null"), Or(Not(Sym("V2=7")), Not(Sym("V3=Nil")))))
          , Or(Sym("V1=Nil"), Sym("V1=null"))
          , Or(Sym("V1=null"), Not(Sym("V1=scala.collection.immutable.::[?]")))
          , Or(Sym("V1=null"), Or(And(Not(Sym("V2=4")), And(Not(Sym("V2=5")), Not(Sym("V2=6")))), Not(Sym("V3=Nil"))))
          , Or(Sym("V1=null"), Or(Not(Sym("V2=1")), Not(Sym("V3=Nil"))))
          , Or(Sym("V1=null"), Or(Not(Sym("V2=2")), Not(Sym("V3=Nil"))))
          , Or(Sym("V1=null"), Or(Not(Sym("V2=7")), Not(Sym("V3=Nil"))))
          , Or(Sym("V1=scala.collection.immutable.::[?]"), Or(Sym("V1=Nil"), Sym("V1=null")))
          , Or(Sym("V1=scala.collection.immutable.::[?]"), Sym("V1=Nil"))
          , Or(Sym("V2=4"), Or(Sym("V2=5"), Sym("V2=6")))
          , Or(Sym("V2=5"), Sym("V2=6"))
          , Or(Sym("V3=Nil"), Sym("V3=null"))
          , Or(Sym("V3=scala.collection.immutable.::[?]"), Or(Sym("V3=Nil"), Sym("V3=null")))
          , Or(Sym("V3=scala.collection.immutable.::[?]"), Sym("V3=Nil"))
          , Sym("V1=Nil")
          , Sym("V1=null")
          , Sym("V1=scala.collection.immutable.::[?]")
          , Sym("V2=4")
          , Sym("V2=5")
          , Sym("V2=6")
          , Sym("V2=7")
          , Sym("V3=Nil")
          , Sym("V3=null")
          , Sym("V3=scala.collection.immutable.::[?]")
        ).sortBy(_.toString.length)

        val formulas0 = Seq(
          Or(Sym("a"), Sym("b"))
          )

        def test = {
          Result.unit(for {
            f <- formulas
          } {
            val expanding = findAllModelsFor(eqFreePropToSolvable(f))
            val tseitin = findAllModelsFor(eqFreePropToSolvableTseitin(f))
            if(formatModels(tseitin) != formatModels(expanding)) {
              println("testing:")
              println(f)
              val tseitin = findAllModelsFor(eqFreePropToSolvableTseitin(f))
            }
            formatModels(tseitin) === formatModels(expanding)
          })
        }
      }
    }
    Outer.Aggregate.test
  }
}
