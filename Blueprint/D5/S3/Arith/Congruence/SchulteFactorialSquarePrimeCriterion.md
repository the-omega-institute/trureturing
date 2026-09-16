# Schulte's Factorial-Square Prime Criterion

## Abstract

Schulte's A006472 divisibility condition characterizes prime natural numbers.

All variables and values lie in the natural numbers N, including zero. The symbol m is the sequence index, n is the criterion input, and a denotes A006472. The operator factorial(x) is x!, powers and products are natural-number operations, subtraction is truncated at zero, and the slash is exact natural-number division. The symbol ∣ denotes natural divisibility, and Prime(n) means that n is prime. Only the Conjecture sentence in Werner Schulte's 2020 comment is settled, for every n at least 2. The proof establishes that every composite n at least 9 divides a(n-1), while the composite cases n < 9 (n = 4, 6, 8) are checked directly. Its odd branch reuses the frozen theorem factorial_dvd_triangular_of_not_odd_prime; the even branch uses double-factorial identities and two-adic quotient bookkeeping.

**Definition 1.1 (The A006472 sequence).**

$$\forall m \in \mathbb{N},\; \operatorname{a}\left(m\right) = (\operatorname{factorial}\left(m\right) \cdot \operatorname{factorial}\left(m - 1\right)) / (2^{m - 1})$$

*Formalization.* `D5/S3/Arith/Congruence/SchulteFactorialSquarePrimeCriterion.a` (`✓ std3`).

*Citation.* Werner Schulte (2020). *OEIS A006472, n!(n-1)!/2^(n-1), with the primality criterion n | 2 a(n-1) + 4 iff n is prime*. URL: <https://oeis.org/A006472>.

*Commentary.*

For each natural m, a(m) is the exact natural quotient of factorial(m) times factorial(m-1) by 2^(m-1). The exactness follows by splitting the required powers of two between the two factorials.

**Theorem 1.2 (Schulte's primality criterion).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow ((n \mid 2 \cdot \operatorname{a}\left(n - 1\right) + 4) \Leftrightarrow (\operatorname{Prime}\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/SchulteFactorialSquarePrimeCriterion.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a006472-schulte-factorial-square-prime-criterion` (proved) by `D5/S3/Arith/Congruence/SchulteFactorialSquarePrimeCriterion.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a006472-schulte-factorial-square-prime-criterion","declaration_gid":"D5/S3/Arith/Congruence/SchulteFactorialSquarePrimeCriterion.result","resolution_kind":"proved"} -->

*Citation.* Werner Schulte (2020). *OEIS A006472, n!(n-1)!/2^(n-1), with the primality criterion n | 2 a(n-1) + 4 iff n is prime*. URL: <https://oeis.org/A006472>.

*Commentary.*

For every natural n at least 2, n divides 2 times a(n-1) plus 4 exactly when n is prime. For primes, Wilson's theorem and Fermat's theorem evaluate the scaled expression modulo n. For composite n at least 9, divisibility of a(n-1) forces any divisibility of the displayed sum to make n divide 4, which is impossible; the smaller composite cases are checked directly.

## References

- Truth anchor: `D5/S3/Arith/Congruence/SchulteFactorialSquarePrimeCriterion.a`
- Truth anchor: `D5/S3/Arith/Congruence/SchulteFactorialSquarePrimeCriterion.result`
- Dependency: [D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue](LaymanOddPowerFactorialResidue.md)
