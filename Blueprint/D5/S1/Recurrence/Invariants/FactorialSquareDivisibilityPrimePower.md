# Exact Factorial-Square Divisibility and Prime Powers

## Abstract

Exact factorial-square divisibility characterizes prime powers.

**Theorem 1.1 (The exact exponent is characterized by prime powers).**

$$\forall n \in \mathbb{N}, 2 \le n \implies (((((n)!)^{n + 1} \mid (n^{2})!) \land (\neg (((n)!)^{n + 2} \mid (n^{2})!))) \iff \operatorname{IsPrimePow}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/FactorialSquareDivisibilityPrimePower.factorial_square_exact_divisibility_iff_prime_power` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a096127-factorial-square-divisibility-prime-power` (proved) by `D5/S1/Recurrence/Invariants/FactorialSquareDivisibilityPrimePower.factorial_square_exact_divisibility_iff_prime_power`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a096127-factorial-square-divisibility-prime-power","declaration_gid":"D5/S1/Recurrence/Invariants/FactorialSquareDivisibilityPrimePower.factorial_square_exact_divisibility_iff_prime_power","resolution_kind":"proved"} -->

*Citation.* Amarnath Murthy (2004). *OEIS A096127, a(n) is the largest k such that (n^2)!/(n!)^k is an integer*. URL: <https://oeis.org/A096127>.

*Commentary.*

Legendre's formula converts each factorial divisibility into a prime-valuation inequality. Base-p digit-sum submultiplicativity bounds the valuation for exponent n+1 and distinguishes exponent n+2 exactly when n is a prime power.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/FactorialSquareDivisibilityPrimePower.factorial_square_exact_divisibility_iff_prime_power`
