# A Multiple with Fewer than Twice as Many Divisors Divides the Square

## Abstract

A multiple whose divisor count stays below twice that of the original divides its square, because one prime exponent exceeding twice its original value, or one new prime, already doubles the divisor count on its own.

**Definition 1.1 (The conjectured divisibility).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; ((n \mid m) \land (tau(m) < 2 \cdot tau(n))) \Rightarrow (m \mid n \cdot n))$$

*Formalization.* `D5/S3/Factorization/DivisorDoublingMultipleDividesSquare.claim` (`✓ std3`).

*Citation.* J. Lowell (2013). *OEIS A225004, a(n) is the largest multiple of n with fewer than twice as many divisors as n*. URL: <https://oeis.org/A225004>.

*Commentary.*

The source names, for each number, the largest of its multiples whose divisor count stays below twice its own, and asserts that this largest multiple divides the square. Recorded here is the statement for every such multiple, not only the largest. Naming the largest one needs a bound on how far to look, and the only natural bound is the square itself, so a literal rendering would assume what is to be shown. The form below contains the assertion and shows in addition that these multiples are finitely many, so the largest exists.

**Theorem 1.2 (The divisibility holds).**

$$\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; ((n \mid m) \land (tau(m) < 2 \cdot tau(n))) \Rightarrow (m \mid n \cdot n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/DivisorDoublingMultipleDividesSquare.result` (`✓ std3`). ∎

*Resolves.* `Problems/divisor-doubling-multiple-divides-square` (proved) by `D5/S3/Factorization/DivisorDoublingMultipleDividesSquare.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"divisor-doubling-multiple-divides-square","declaration_gid":"D5/S3/Factorization/DivisorDoublingMultipleDividesSquare.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* J. Lowell (2013). *OEIS A225004, a(n) is the largest multiple of n with fewer than twice as many divisors as n*. URL: <https://oeis.org/A225004>.

*Commentary.*

The divisor count is the product over the primes of one more than each exponent, and divisibility by the square is the pointwise bound of each exponent by twice its original. Suppose one prime broke that bound. If it is a prime of the multiple only, split the product at the boundary between the original primes and the rest: the first part is already at least the original count factorwise, and the second contains a factor of at least two at the offending prime. If it is a prime of both, then one more than its exponent in the multiple is at least twice one more than its exponent in the original, so pulling that prime out of the product supplies the factor of two while every remaining factor is at least its counterpart. Either way the divisor count of the multiple reaches twice the original, against the hypothesis. So no prime breaks the bound and the divisibility follows.

## References

- Truth anchor: `D5/S3/Factorization/DivisorDoublingMultipleDividesSquare.claim`
- Truth anchor: `D5/S3/Factorization/DivisorDoublingMultipleDividesSquare.result`
