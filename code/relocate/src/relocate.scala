package isabelle


object Relocate {
  object Source_Line extends Scala.Fun_Strings("source_line") {
    val here = Scala_Project.here
    def apply(args: List[String]): List[String] = {
      val (id, offset) = args match {
        case id :: offset :: Nil => (id, Value.Int.parse(offset))
        case _ => error("Invalid arguments")
      }
      val line = jedit.PIDE.snapshot().find_command_line(Value.Long.parse(id), offset)
      List(line.getOrElse(error("No line")).toString)
    }
  }
}

class Relocate_Functions extends Scala.Functions(Relocate.Source_Line)
