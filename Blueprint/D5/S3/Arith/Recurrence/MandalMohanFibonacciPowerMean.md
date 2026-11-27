# Mandal and Mohan's Fibonacci Power Means

## Abstract

Integrality of the quotient in Mandal and Mohan's Conjecture 1.19.

**Theorem 1.1 (Conjecture 1.19 holds for all positive prefix lengths and exponents at least three).**

$$\forall n,k\in\mathbb{N}, (1\le n \land 3\le k) \implies ((\exists q\in\mathbb{N}, \frac{n^{k}}{\sum_{i=1}^{n} \frac{1}{F_{i}^{k}}}=(q:\mathbb{Q})) \iff (n=1 \lor n=2))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Recurrence/MandalMohanFibonacciPowerMean.result` (`✓ std3`). ∎

*Resolves.* `Problems/mandal-mohan-fibonacci-power-means-1-19` (proved) by `D5/S3/Arith/Recurrence/MandalMohanFibonacciPowerMean.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mandal-mohan-fibonacci-power-means-1-19","declaration_gid":"D5/S3/Arith/Recurrence/MandalMohanFibonacciPowerMean.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sagar Mandal and Mohan (2026). *Integral Means of Fibonacci Numbers: Divisibility, Density, and Arithmetic Structure*. DOI: [10.48550/arXiv.2611.32519](https://doi.org/10.48550/arXiv.2611.32519). URL: <https://arxiv.org/html/2611.32519v1#S1.Thmtheorem19>.

*Commentary.*

The Fibonacci numbers are indexed with F(1) = F(2) = 1. The sum includes both endpoints and all division takes place in the rationals. At prefix lengths one and two the quotients are 1 and 2 raised to the exponent minus one, respectively.

The condition n ≥ 1 keeps the prefix nonempty. The source quotient is undefined for the empty prefix because its denominator is zero. With Lean's totalized rational division, n = 0 and k = 3 give the natural value 0, which lies outside the stated classification of prefix lengths. The condition k ≥ 3 excludes the case n = 3 and k = 2, where the quotient is 9 / (1 + 1 + 1/4) = 4 and the prefix length again lies outside the classification.

For a prefix of length at least eleven, Bertrand's postulate gives a prime index r strictly above the ceiling of half the length. A prime p dividing F(r) has first zero index r. The Fibonacci rank bound and parity give p at least 2r − 1, hence larger than the prefix length. Only F(r) in the prefix is divisible by p. Clearing denominators makes the sum of the scaled reciprocal powers coprime to p, so an integral quotient would be divisible by p raised to the exponent. The quotient is positive and strictly below the prefix length raised to the same exponent.

Lengths five through ten use explicit unique maximal prime powers 5, 8, or 13. At length four the cleared denominator is greater than one and coprime to 24. At length three it would have to be a power of three. Reduction modulo eight and factorization of a difference of squares then force the exponent to be two.

## References

- Truth anchor: `D5/S3/Arith/Recurrence/MandalMohanFibonacciPowerMean.result`
