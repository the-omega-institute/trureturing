# Finite Fibonacci rank closure

## Abstract

The prime support of Fibonacci entry ranks has a bounded least closure over every finite set of primes greater than five.

For a prime p, its Fibonacci entry rank is the least positive index r for which p divides F_r. The first-entry divisibility theorem and the golden Frobenius zero supply this rank. The construction below follows prime factors of these actual ranks.

**Definition 1.1 (Least positive zero witness).**

Lean statement: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.rankWitness`

*Formalization.* `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.rankWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each prime p, this witness gives a positive index r with p dividing F_r, together with a proof that every other positive zero index is at least r.

**Definition 1.2 (The original entry rank).**

Lean statement: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.fibonacciRank`

*Formalization.* `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.fibonacciRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a prime p, this value is the least positive r with p dividing F_r. Its value at a nonprime input is one, so it contributes no prime factors to the closure operation.

**Definition 1.3 (Initial prime set).**

Lean statement: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.rankClosureSeed`

*Formalization.* `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.rankClosureSeed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial set consists of the prescribed finite set together with the primes two, three and five.

**Definition 1.4 (Prime-support expansion).**

Lean statement: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.rankClosureStep`

*Formalization.* `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.rankClosureStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One step retains each current prime and adjoins every prime divisor of its Fibonacci entry rank.

**Definition 1.5 (Iterated closure).**

Lean statement: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.fibonacciRankClosure`

*Formalization.* `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.fibonacciRankClosure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let B be the larger of five and the largest member of the prescribed set. Starting from the initial set, apply the expansion once per prime at most B. This gives a finite, explicitly determined set.

**Theorem 1.6 (Bounded least closure).**

Lean statement: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.finite_fibonacci_rank_closure`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.finite_fibonacci_rank_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite set S of primes greater than five, the iterated closure contains S and the three small primes, contains only primes at most B, and is unchanged by one further expansion. It is contained in every expansion-closed finite set that contains the same initial primes. Indeed, a prime divisor of the rank of p is smaller than p when p exceeds five; the ranks at two, three and five contribute only primes at most five. The expanding sets therefore stay inside the finite universe of primes at most B. Equal cardinalities on successive steps give a fixed point, and induction gives its leastness.

## References

- Truth anchor: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.fibonacciRank`
- Truth anchor: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.fibonacciRankClosure`
- Truth anchor: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.finite_fibonacci_rank_closure`
- Truth anchor: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.rankClosureSeed`
- Truth anchor: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.rankClosureStep`
- Truth anchor: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.rankWitness`
