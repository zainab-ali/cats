package cats
package jvm
package tests

import cats.kernel.laws.GroupLaws
import cats.laws.discipline._
import cats.laws.discipline.arbitrary._
import cats.tests.{CatsSuite, ListWrapper}

import scala.concurrent.{Await, Future}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

import org.scalacheck.Arbitrary
import org.scalacheck.Arbitrary.arbitrary

class FutureTests extends CatsSuite {
  val timeout = 3.seconds

  def futureEither[A](f: Future[A]): Future[Either[Throwable, A]] =
    f.map(Either.right[Throwable, A]).recover { case t => Either.left(t) }

  implicit def eqfa[A: Eq]: Eq[Future[A]] =
    new Eq[Future[A]] {
      def eqv(fx: Future[A], fy: Future[A]): Boolean = {
        val fz = futureEither(fx) zip futureEither(fy)
        Await.result(fz.map { case (tx, ty) => tx === ty }, timeout)
      }
    }

  implicit val throwableEq: Eq[Throwable] =
    Eq[String].on(_.toString)

  // Need non-fatal Throwables for Future recoverWith/handleError
  implicit val nonFatalArbitrary: Arbitrary[Throwable] =
    Arbitrary(arbitrary[Exception].map(identity))

  checkAll("Future with Throwable", MonadErrorTests[Future, Throwable].monadError[Int, Int, Int])
  checkAll("Future", MonadTests[Future].monad[Int, Int, Int])

  {
    implicit val F = ListWrapper.semigroup[Int]
    checkAll("Future[ListWrapper[Int]]", GroupLaws[Future[ListWrapper[Int]]].semigroup)
  }

  checkAll("Future[Int]", GroupLaws[Future[Int]].monoid)
}
