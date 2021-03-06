package org.jetbrains.plugins.scala.project

/**
  * @author Pavel Fatin
  */
sealed abstract class Platform(val getName: String) extends Named {
  override def toString: String = getName
}

object Platform {

  final case object Scala extends Platform("Scala")

  final case object Dotty extends Platform("Dotty")
}