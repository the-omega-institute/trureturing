# Positive values of A399155 have finite fibers

## Abstract

Every positive integer value of the prime-factor subtraction difference occurs at only finitely many indices.

The proof uses the prior smallest-factor formula from OEIS A175126 and largest-factor bound from OEIS A309892. The repository's existing A399155 triage distinguishes their comparison consequence from the separate positive-value fiber-finiteness observation.

**Definition 1.1 (Smallest-factor walk).**

Lean statement: `D5/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness.stepsSmallest`

*Formalization.* `D5/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness.stepsSmallest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The step count is zero below two. At every other natural value n, subtract n.minFac and add one to the step count of the resulting value. A prime divisor also divides the value after its subtraction, so a walk beginning at least two never visits one.

**Definition 1.2 (Largest-factor walk).**

Lean statement: `D5/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness.stepsLargest`

*Formalization.* `D5/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness.stepsLargest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The step count is zero below two. At every other natural value n, subtract its largest prime factor and add one to the step count of the resulting value. The largest-factor function reuses CenteredReducedResidueProgressions.GreatestPrimeFactor, whose definition is exactly the supremum of n.primeFactors with the identity map.

**Definition 1.3 (The integer-valued difference).**

Lean statement: `D5/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness.a`

*Formalization.* `D5/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sequence value is the smallest-factor step count minus the largest-factor step count, with both counts interpreted as integers. The subtraction is integer subtraction rather than truncated natural subtraction.

**Definition 1.4 (The exact finite-fiber assertion).**

$$\forall v \in \mathbb{Z}, 0 < v \implies \operatorname{Finite}\left(\{n \in \mathbb{N} \mid 2 \le n \land \operatorname{a}\left(n\right) = v\}\right)$$

*Formalization.* `D5/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every positive integer v, the natural indices n at least two satisfying a(n)=v form a finite set. The two walk definitions and their integer-valued difference a are defined in this module.

**Theorem 1.5 (Each positive value is attained only finitely often).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a399155-value-finiteness` (proved) by `D5/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a399155-value-finiteness","declaration_gid":"D5/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

At a prime index both walks take one step, so their difference is zero. For composite n at least six, the lower estimate is 6a(n)+3sqrt(n)+3 at least n, where sqrt is the natural square root. For every n at least six, three times the largest-factor step count is at most n+1. If its largest factor is at least three, this follows directly from the weighted bound. Otherwise that factor equals two: the smallest prime factor of n/2 is at most two, forcing four to divide n. Then (n-2)/2 is odd and at least three, so an odd prime divisor shows that the largest factor of n-2 is at least three. Charge the first step separately and apply the weighted bound to the remainder. At an odd composite index its smallest factor is at most sqrt(n). The exact smallest-factor counts give the displayed lower bound in both parities. For a positive value v, put t=sqrt(n). The inequalities t squared at most n and n at most 6v+3t+3 give t at most 6v+6 and n at most 24v+21. Prime indices cannot occur, and the small indices satisfy the same final bound, so the fiber is a subset of a finite natural interval.

## References

- Truth anchor: `D5/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness.a`
- Truth anchor: `D5/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness.claim`
- Truth anchor: `D5/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness.result`
- Truth anchor: `D5/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness.stepsLargest`
- Truth anchor: `D5/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness.stepsSmallest`
- Dependency: [D5/S3/ArithUnits/CenteredReducedResidueProgressions](../../ArithUnits/CenteredReducedResidueProgressions.md)
