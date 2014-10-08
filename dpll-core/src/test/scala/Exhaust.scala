object Exhaust extends App {

  sealed abstract class Deep

  case object Ga extends Deep

  sealed class Gp extends Deep

  case object Gu extends Gp

  def ma4(x: Deep) = x match {
    // missing cases: Gu, Gp
    case Ga => println("Ga")
    case _: Gp => println("Gp")
    case Gu => println("Gu")
  }

  println(ma4(Gu))
//  println(ma4(Ga))
}
