import sbt._

object DependencyManagement {

  /** Excluded and version managed transitive artifacts */
  def ivyExclusionsAndOverrides =
    <dependencies>
      <exclude org="org.junit" rev="*"/>
      <exclude org="org.junit" rev="4.8.1"/>
      <exclude org="colt" rev="1.2.0"/>
      <exclude org="blas" module="blas" rev="*"/>
      <exclude org="javax.script" rev="*"/>
      <exclude org="org.scala-tools.testing" module="scalacheck_2.8.0" rev="1.7"/>
      <override org="junit" module="junit" rev="4.8.1"/>
      <exclude org="org.eclipse" rev="*"/>
    </dependencies>

  /** Utilities for File IO */
  def CommonsIo = "commons-io" % "commons-io" % "2.4"

  /** General utilities for Java language */
  def CommonsLang = "commons-lang" % "commons-lang" % "2.4"

  /** Scala library providing Actors and Promises (for concurrency), and functional programming tools */
  def ScalazCore = "org.scalaz" %% "scalaz-core" % "7.0.0"
  def ScalazConcurrent = "org.scalaz" %% "scalaz-concurrent" % "7.0.0"
  def ScalazEffect = "org.scalaz" %% "scalaz-effect" % "7.0.0"

  def SpringCore = "org.springframework" % "spring-core" % "2.5.6"

  /**
   * Specs, unit testing framework
   *
   * http://code.google.com/p/specs/
   */
  def Specs = "org.specs2" %% "specs2" % "2.0" % "test" intransitive()

  def SpecsDeps= Seq(ScalazCore, ScalazConcurrent, ScalazEffect, Scalacheck, MockitoAll)

  def JUnit = "junit" % "junit" % "4.8.1" % "test" intransitive()

  /**
   * Scalacheck, automated unit testing using randomized test cases.
   *
   * http://code.google.com/p/scalacheck/
   *
   * We use this through Specs.
   */
  def Scalacheck = "org.scalacheck" %% "scalacheck" % "1.10.0" % "test"

  /**
   * Sat4j: the boolean satisfaction and optimization library for Java
   *
   * http://www.sat4j.org/
   */
  def Sat4j = "org.sat4j" % "org.sat4j.core" % "2.3.1"

  /** Dependency of Specs */
  def MockitoAll = "org.mockito" % "mockito-all" % "1.9.0" % "test"
}
