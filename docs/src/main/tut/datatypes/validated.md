---
layout: docs
title:  "Validated"
section: "data"
source: "core/src/main/scala/cats/data/Validated.scala"
scaladoc: "#cats.data.Validated"
---
# Validated

Imagine you are filling out a web form to signup for an account. You input your username and password and submit.
Response comes back saying your username can't have dashes in it, so you make some changes and resubmit. Can't
have special characters either. Change, resubmit. Passwords need to have at least one capital letter. Change,
resubmit. Password needs to have at least one number.

The code validating the form might look something like this:

```tut:book

case class Form(username: String, password: String)

sealed trait ValidationFailure
case class DashesPresent(text: String) extends ValidationFailure
case class NoCapitals(text: String) extends ValidationFailure
case class NoNumbers(text: String) extends ValidationFailure

def validateForm(form: Form): Either[ValidationFailure, Form] =
for {
  _ <- checkNoDashes(form.username)
  _ <- checkAtLeastOneCapital(form.password)
  _ <- checkAtLeastOneNumber(form.password)
  } yield form
  
def checkNoDashes(s: String): Either[ValidationFailure, String] = if(s.contains("-") Either.left(DashesPresent(s)) else Either.right(s)
def checkAtLeastOneCapital(s: String): Either[ValidationFailure, String] = Either.fromOption([A-Z]+".r.findFirstIn(s), NoCapitals(s))
def checkAtLeastOneNumber(s: String): Either[ValidationFailure, String] = Either.fromOption([0-9]+".r.findFirstIn(s), NoNumbers(s))

```

The code may be clean and functional, but someone using it could get frustrated by having to resubmit the form, only to discover that validation failed at a later stage.
It would be much nicer to have all of these errors reported simultaneously, on the first form submission.

Enter `Validated`.

## Parallel validation

The `Validated` data type is used to collect errors, such that they can be reported all at once.
It can be used in a similar way to `Either`, but has a few key differences:
`Either` has a *Monad* instance, so it can execute dependent checks sequentially, and terminates on encountering an error
`Validated` has an *Applicative* instance, so can execute independent checks and collects all errors

Just as `Either` can be a `Left` or a `Right`, `Validated` can be `Invalid` or `Valid`.

Our checks can be executed independently of each other, so we can use a `Validated`.

Let's first write our checks in terms of `Valid` and `Invalid`:

```tut:book
def checkNoDashes(s: String): Either[ValidationFailure, String] = if(s.contains("-") DashesPresent(s).invalidNel else s.valid
def checkAtLeastOneCapital(s: String): Either[ValidationFailure, String] = Validated.fromOption([A-Z]+".r.findFirstIn(s), NoCapitals(s))
def checkAtLeastOneNumber(s: String): Either[ValidationFailure, String] = Validated.fromOption([0-9]+".r.findFirstIn(s), NoNumbers(s))
```

Notice that we've used a method called `invalidNel`.  This creates a non-empty list on the left.
So our validated instance can actually store a list of errors instead of a single one.

We can now validate the form at once:
```tut:book

def validateForm(form: Form): Either[ValidationFailure, Form] = 
((checkNoDashes(form.username)), checkAtLeastOneCapital(form.password), checkAtLeastOneCapital(form.password)).map3 {
  case (username, password, password) => form
}
```

Let's try submitting a form again:

We can now see everything that's failed.

## How does this work?



Now we are ready to write our parser.

```tut:silent
import cats.data.Validated
import cats.data.Validated.{Invalid, Valid}

case class Config(map: Map[String, String]) {
  def parse[A : Read](key: String): Validated[ConfigError, A] =
    map.get(key) match {
      case None        => Invalid(MissingConfig(key))
      case Some(value) =>
        Read[A].read(value) match {
          case None    => Invalid(ParseError(key))
          case Some(a) => Valid(a)
        }
    }
}
```

Everything is in place to write the parallel validator. Recall that we can only do parallel
validation if each piece is independent. How do we enforce the data is independent? By asking
for all of it up front. Let's start with two pieces of data.

```tut:silent
def parallelValidate[E, A, B, C](v1: Validated[E, A], v2: Validated[E, B])(f: (A, B) => C): Validated[E, C] =
  (v1, v2) match {
    case (Valid(a), Valid(b))       => Valid(f(a, b))
    case (Valid(_), i@Invalid(_))   => i
    case (i@Invalid(_), Valid(_))   => i
    case (Invalid(e1), Invalid(e2)) => ???
  }
```

We've run into a problem. In the case where both have errors, we want to report both. But we have
no way of combining the two errors into one error! Perhaps we can put both errors into a `List`,
but that seems needlessly specific - clients may want to define their own way of combining errors.

How then do we abstract over a binary operation? The `Semigroup` type class captures this idea.

```tut:silent
import cats.Semigroup

def parallelValidate[E : Semigroup, A, B, C](v1: Validated[E, A], v2: Validated[E, B])(f: (A, B) => C): Validated[E, C] =
  (v1, v2) match {
    case (Valid(a), Valid(b))       => Valid(f(a, b))
    case (Valid(_), i@Invalid(_))   => i
    case (i@Invalid(_), Valid(_))   => i
    case (Invalid(e1), Invalid(e2)) => Invalid(Semigroup[E].combine(e1, e2))
  }
```

Perfect! But.. going back to our example, we don't have a way to combine `ConfigError`s. But as clients,
we can change our `Validated` values where the error can be combined, say, a `List[ConfigError]`. It is
more common however to use a `NonEmptyList[ConfigError]` - the `NonEmptyList` statically guarantees we
have at least one value, which aligns with the fact that if we have an `Invalid`, then we most
certainly have at least one error. This technique is so common there is a convenient method on `Validated`
called `toValidatedNel` that turns any `Validated[E, A]` value to a `Validated[NonEmptyList[E], A]`.
Additionally, the type alias `ValidatedNel[E, A]` is provided.

Time to parse.

```tut:silent
import cats.SemigroupK
import cats.data.NonEmptyList
import cats.implicits._

case class ConnectionParams(url: String, port: Int)

val config = Config(Map(("endpoint", "127.0.0.1"), ("port", "not an int")))

implicit val nelSemigroup: Semigroup[NonEmptyList[ConfigError]] =
  SemigroupK[NonEmptyList].algebra[ConfigError]

implicit val readString: Read[String] = Read.stringRead
implicit val readInt: Read[Int] = Read.intRead
```

Any and all errors are reported!

```tut:book
val v1 = parallelValidate(config.parse[String]("url").toValidatedNel,
                          config.parse[Int]("port").toValidatedNel)(ConnectionParams.apply)

val v2 = parallelValidate(config.parse[String]("endpoint").toValidatedNel,
                          config.parse[Int]("port").toValidatedNel)(ConnectionParams.apply)

val config = Config(Map(("endpoint", "127.0.0.1"), ("port", "1234")))
val v3 = parallelValidate(config.parse[String]("endpoint").toValidatedNel,
                          config.parse[Int]("port").toValidatedNel)(ConnectionParams.apply)
```

## Apply
Our `parallelValidate` function looks awfully like the `Apply#map2` function.

```scala
def map2[F[_], A, B, C](fa: F[A], fb: F[B])(f: (A, B) => C): F[C]
```

Which can be defined in terms of `Apply#ap` and `Apply#map`, the very functions needed to create an `Apply` instance.

Can we perhaps define an `Apply` instance for `Validated`? Better yet, can we define an `Applicative` instance?

*Note*: the example below assumes usage of the [kind-projector compiler plugin](https://github.com/non/kind-projector) and will not compile if it is not being used in a project.

```tut:silent
import cats.Applicative

implicit def validatedApplicative[E : Semigroup]: Applicative[Validated[E, ?]] =
  new Applicative[Validated[E, ?]] {
    def ap[A, B](f: Validated[E, A => B])(fa: Validated[E, A]): Validated[E, B] =
      (fa, f) match {
        case (Valid(a), Valid(fab)) => Valid(fab(a))
        case (i@Invalid(_), Valid(_)) => i
        case (Valid(_), i@Invalid(_)) => i
        case (Invalid(e1), Invalid(e2)) => Invalid(Semigroup[E].combine(e1, e2))
      }

    def pure[A](x: A): Validated[E, A] = Validated.valid(x)
  }
```

Awesome! And now we also get access to all the goodness of `Applicative`, which includes `map{2-22}`, as well as the
`Cartesian` syntax `|@|`.

We can now easily ask for several bits of configuration and get any and all errors returned back.

```tut:silent
import cats.Apply
import cats.data.ValidatedNel

implicit val nelSemigroup: Semigroup[NonEmptyList[ConfigError]] =
  SemigroupK[NonEmptyList].algebra[ConfigError]

val config = Config(Map(("name", "cat"), ("age", "not a number"), ("houseNumber", "1234"), ("lane", "feline street")))

case class Address(houseNumber: Int, street: String)
case class Person(name: String, age: Int, address: Address)
```

Thus.

```tut:book
val personFromConfig: ValidatedNel[ConfigError, Person] =
  Apply[ValidatedNel[ConfigError, ?]].map4(config.parse[String]("name").toValidatedNel,
                                           config.parse[Int]("age").toValidatedNel,
                                           config.parse[Int]("house_number").toValidatedNel,
                                           config.parse[String]("street").toValidatedNel) {
    case (name, age, houseNumber, street) => Person(name, age, Address(houseNumber, street))
  }
```

## Of `flatMap`s and `Either`s
`Option` has `flatMap`, `Either` has `flatMap`, where's `Validated`'s? Let's try to implement it - better yet,
let's implement the `Monad` type class.

```tut:silent
import cats.Monad

implicit def validatedMonad[E]: Monad[Validated[E, ?]] =
  new Monad[Validated[E, ?]] {
    def flatMap[A, B](fa: Validated[E, A])(f: A => Validated[E, B]): Validated[E, B] =
      fa match {
        case Valid(a)     => f(a)
        case i@Invalid(_) => i
      }

    def pure[A](x: A): Validated[E, A] = Valid(x)

    @annotation.tailrec
    def tailRecM[A, B](a: A)(f: A => Validated[E, Either[A, B]]): Validated[E, B] =
      f(a) match {
        case Valid(Right(b)) => Valid(b)
        case Valid(Left(a)) => tailRecM(a)(f)
        case i@Invalid(_) => i
      }
  }
```

Note that all `Monad` instances are also `Applicative` instances, where `ap` is defined as

```tut:silent
trait Monad[F[_]] {
  def flatMap[A, B](fa: F[A])(f: A => F[B]): F[B]
  def pure[A](x: A): F[A]

  def map[A, B](fa: F[A])(f: A => B): F[B] =
    flatMap(fa)(f.andThen(pure))

  def ap[A, B](fa: F[A])(f: F[A => B]): F[B] =
    flatMap(fa)(a => map(f)(fab => fab(a)))
}
```

However, the `ap` behavior defined in terms of `flatMap` does not behave the same as that of
our `ap` defined above. Observe:

```tut:book
val v = validatedMonad.tuple2(Validated.invalidNel[String, Int]("oops"), Validated.invalidNel[String, Double]("uh oh"))
```

This one short circuits! Therefore, if we were to define a `Monad` (or `FlatMap`) instance for `Validated` we would
have to override `ap` to get the behavior we want. But then the behavior of `flatMap` would be inconsistent with
that of `ap`, not good. Therefore, `Validated` has only an `Applicative` instance.

## `Validated` vs `Either`

We've established that an error-accumulating data type such as `Validated` can't have a valid `Monad` instance. Sometimes the task at hand requires error-accumulation. However, sometimes we want a monadic structure that we can use for sequential validation (such as in a for-comprehension). This leaves us in a bit of a conundrum.

Cats has decided to solve this problem by using separate data structures for error-accumulation (`Validated`) and short-circuiting monadic behavior (`Either`).

If you are trying to decide whether you want to use `Validated` or `Either`, a simple heuristic is to use `Validated` if you want error-accumulation and to otherwise use `Either`.

## Sequential Validation

If you do want error accumulation but occasionally run into places where you sequential validation is needed, then `Validated` provides a couple methods that may be helpful.

### `andThen`
The `andThen` method is similar to `flatMap` (such as `Either.flatMap`). In the cause of success, it passes the valid value into a function that returns a new `Validated` instance.

```tut:book
val houseNumber = config.parse[Int]("house_number").andThen{ n =>
   if (n >= 0) Validated.valid(n)
   else Validated.invalid(ParseError("house_number"))
}
```

### `withEither`
The `withEither` method allows you to temporarily turn a `Validated` instance into an `Either` instance and apply it to a function.

```tut:silent
import cats.syntax.either._ // get Either#flatMap

def positive(field: String, i: Int): Either[ConfigError, Int] = {
  if (i >= 0) Right(i)
  else Left(ParseError(field))
}
```

Thus.

```tut:book
val houseNumber = config.parse[Int]("house_number").withEither{ either: Either[ConfigError, Int] =>
  either.flatMap{ i =>
    positive("house_number", i)
  }
}
```
