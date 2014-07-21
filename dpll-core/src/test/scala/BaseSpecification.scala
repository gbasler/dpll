import org.specs2.execute.PendingUntilFixed
import org.specs2.mutable.Specification
import org.specs2.ScalaCheck

trait BaseSpecification extends Specification
with ScalaCheck
with PendingUntilFixed {

  sequential
}
