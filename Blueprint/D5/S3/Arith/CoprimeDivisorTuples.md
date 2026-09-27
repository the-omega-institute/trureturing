# Pairwise Coprime Tuples of Divisors Count the Divisors of a Self Power

## Abstract

Pairwise coprime ordered tuples of divisors of a number are counted by a product over its primes, and at tuple length equal to the number itself that product counts the divisors of the number raised to itself.

**Definition 1.1 (Tuples of divisors that are pairwise coprime).**

$$coprimeDivisorTuples(k, n) = \{f \mid (\forall i \in Fin k,\; f(i) \mid n) \land (\forall i \in Fin k,\; \forall j \in Fin k,\; (i \ne j) \Rightarrow (\gcd (f(i), f(j)) = 1))\}$$

*Formalization.* `D5/S3/Arith/CoprimeDivisorTuples.coprimeDivisorTuples` (`✓ std3`).

*Citation.* Gus Wiseman (2021). *OEIS A062319, Number of divisors of n^n, or of A000312(n)*. URL: <https://oeis.org/A062319>.

*Commentary.*

A tuple of the stated length assigns a divisor of the number to each index. It is pairwise coprime when any two coordinates at distinct indices have greatest common divisor one. Nothing forbids the value one, and nothing forbids it from repeating, so the constant tuple of ones always belongs; the order of the coordinates matters, so a pair and its transpose are counted separately. The worked lists printed on the source entry for the lengths one through five fix both readings. The length is carried as a parameter separate from the number, because the count is a product over the primes of the number only once the length is held fixed; tying the length to the number destroys that independence.

**Definition 1.2 (The conjectured identity).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; (0 < n) \Rightarrow (\lvert coprimeDivisorTuples(n, n) \rvert = \lvert divisors(n^{n}) \rvert))$$

*Formalization.* `D5/S3/Arith/CoprimeDivisorTuples.claim` (`✓ std3`).

*Citation.* Gus Wiseman (2021). *OEIS A062319, Number of divisors of n^n, or of A000312(n)*. URL: <https://oeis.org/A062319>.

*Commentary.*

The source asserts that for a positive number, the pairwise coprime ordered tuples of divisors whose length equals the number itself are as many as the divisors of the number raised to its own power, and reports the assertion checked as far as thirty.

**Theorem 1.3 (The identity holds).**

$$\forall n \in \mathrm{Nat},\; (0 < n) \Rightarrow (\lvert coprimeDivisorTuples(n, n) \rvert = \lvert divisors(n^{n}) \rvert)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CoprimeDivisorTuples.result` (`✓ std3`). ∎

*Resolves.* `Problems/coprime-divisor-tuples` (proved) by `D5/S3/Arith/CoprimeDivisorTuples.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"coprime-divisor-tuples","declaration_gid":"D5/S3/Arith/CoprimeDivisorTuples.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman (2021). *OEIS A062319, Number of divisors of n^n, or of A000312(n)*. URL: <https://oeis.org/A062319>.

*Commentary.*

Both sides are the same product over the primes dividing the number. For the right side, the exponent of a prime in the self power is the number times its exponent in the number, so the divisor count of the self power is the product over the primes of one more than the number times the exponent. For the left side, pairwise coprimality says exactly that each prime dividing the number divides at most one coordinate. A tuple therefore splits into one independent choice per prime: either no coordinate carries the prime, which is one possibility, or a single coordinate carries it to an exponent between one and its exponent in the number, which is the length times that exponent. Summing the two cases gives the same factor at every prime. The argument is carried out by identifying a divisor with its bounded exponent vector, reading coprimality as the absence of a prime with positive exponent on both sides, and identifying a column of the exponent matrix with either the empty choice or a pair consisting of a coordinate and a positive exponent. Holding the length fixed and letting the number vary proves more than was asserted: for every length the count is the corresponding product, and the source assertion is the diagonal where the length equals the number. The number one needs no separate treatment, since its set of primes is empty and the empty product is one.

## References

- Truth anchor: `D5/S3/Arith/CoprimeDivisorTuples.claim`
- Truth anchor: `D5/S3/Arith/CoprimeDivisorTuples.coprimeDivisorTuples`
- Truth anchor: `D5/S3/Arith/CoprimeDivisorTuples.result`
