package fpinscala.state

trait RNG {
  def nextInt: (Int, RNG) // Should generate a random `Int`. We'll later define other functions in terms of `nextInt`.
}

object RNG {
  // NB - this was called SimpleRNG in the book text

  case class Simple(seed: Long) extends RNG {
    def nextInt: (Int, RNG) = {
      val newSeed = (seed * 0x5DEECE66DL + 0xBL) & 0xFFFFFFFFFFFFL // `&` is bitwise AND. We use the current seed to generate a new seed.
      val nextRNG = Simple(newSeed) // The next state, which is an `RNG` instance created from the new seed.
      val n = (newSeed >>> 16).toInt // `>>>` is right binary shift with zero fill. The value `n` is our new pseudo-random integer.
      (n, nextRNG) // The return value is a tuple containing both a pseudo-random integer and the next `RNG` state.
    }
  }

  type Rand[+A] = RNG => (A, RNG)

  val int: Rand[Int] = _.nextInt

  def unit[A](a: A): Rand[A] =
    rng => (a, rng)

  def map[A, B](s: Rand[A])(f: A => B): Rand[B] =
    rng => {
      val (a, rng2) = s(rng)
      (f(a), rng2)
    }

  def nonNegativeInt(rng: RNG): (Int, RNG) = {
    val (n, rand) = rng.nextInt
    val nonNegative = if (n < 0) -(n + 1) else n
    (nonNegative, rand)
  }

  def double(rng: RNG): (Double, RNG) = {
    val (nonNeg, rng2) = nonNegativeInt(rng)
    (nonNeg / (Int.MaxValue.toDouble + 1), rng2)
  }

  def otherDouble(rng: RNG): Rand[Double] = {
    map(nonNegativeInt)(_ / (Int.MaxValue.toDouble + 1))
  }

  def intDouble(rng: RNG): ((Int, Double), RNG) = {
    val (n, rng2) = rng.nextInt
    val (n2, rng3) = double(rng2)
    ((n, n2), rng3)
  }

  def doubleInt(rng: RNG): ((Double, Int), RNG) = {
    val ((i, d), rng1) = intDouble(rng)
    ((d, i), rng1)
  }

  def double3(rng: RNG): ((Double, Double, Double), RNG) = {
    val (n, rng2) = double(rng)
    val (n2, rng3) = double(rng2)
    val (n3, rng4) = double(rng3)
    ((n, n2, n3), rng4)
  }

  def ints(count: Int)(rng: RNG): (List[Int], RNG) = {
    if (count == 0) {
      (List.empty, rng)
    } else {
      val (i, r) = rng.nextInt
      val (list, r2) = ints(count - 1)(r)
      (List(i) ++ list, r2)
    }
  }

  def map2[A, B, C](ra: Rand[A], rb: Rand[B])(f: (A, B) => C): Rand[C] = {}

  def sequence[A](fs: List[Rand[A]]): Rand[List[A]] = ???

  def flatMap[A, B](f: Rand[A])(g: A => Rand[B]): Rand[B] = ???
}

case class State[S, +A](run: S => (A, S)) {
  def map[B](f: A => B): State[S, B] =
    ???
  def map2[B, C](sb: State[S, B])(f: (A, B) => C): State[S, C] =
    ???
  def flatMap[B](f: A => State[S, B]): State[S, B] =
    ???
}

sealed trait Input
case object Coin extends Input
case object Turn extends Input

case class Machine(locked: Boolean, candies: Int, coins: Int)

object State {
  type Rand[A] = State[RNG, A]
  def simulateMachine(inputs: List[Input]): State[Machine, (Int, Int)] = ???
}
