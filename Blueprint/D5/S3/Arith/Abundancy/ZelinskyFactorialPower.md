# Zelinsky Conjecture 36

## Abstract

The Euler product over the prime factors of a factorial power plus one tends to one.

**Definition 1.1 (The distinct-prime Euler product).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyFactorialPower.H`

*Formalization.* `D5/S3/Arith/Abundancy/ZelinskyFactorialPower.H` (`✓ std3`).

*Citation.* J. Zelinsky (2023). *On the small prime factors of a non-deficient number*. URL: <https://math.colgate.edu/~integers/x13/x13.pdf>.

*Commentary.*

For a natural number m, H(m) is the product of p/(p-1) over all distinct prime factors p of m. The empty product is one. This is precisely the function on page three of the source.

**Theorem 1.2 (The factorial-power limit).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyFactorialPower.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyFactorialPower.result` (`✓ std3`). ∎

*Resolves.* `Problems/zelinsky-2023-conjecture-36` (proved) by `D5/S3/Arith/Abundancy/ZelinskyFactorialPower.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zelinsky-2023-conjecture-36","declaration_gid":"D5/S3/Arith/Abundancy/ZelinskyFactorialPower.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* J. Zelinsky (2023). *On the small prime factors of a non-deficient number*. URL: <https://math.colgate.edu/~integers/x13/x13.pdf>.

*Commentary.*

As the natural number n tends to infinity, H((n!)^n+1) tends to one. Every prime factor p of this integer exceeds n. The multiplicative order of n! modulo p is positive and divides both 2n and p-1.

For any positive e, separate primes using the thresholds n^(1+3e), n^3, and the order threshold n^e. Mertens' reciprocal-prime estimate bounds the first range by log(1+3e) plus a term tending to zero. Small orders place the primes among divisors of (n!)^d-1. The logarithmic budget for distinct prime factors bounds this contribution. Large orders place primes in progressions 1+kd; the harmonic sum bound and the divisor subpower estimate control their total. The final range is controlled by the logarithm of (n!)^n+1. All three remaining bounds tend to zero.

Letting e approach zero makes the complete reciprocal-prime sum tend to zero. The logarithm of each Euler factor lies between zero and 2/p, so exponentiation gives the stated limit. This proves exactly Conjecture 36. Limits for other exponents or the minus sign are not additional conclusions of this theorem.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyFactorialPower.H`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyFactorialPower.result`
- Dependency: [D5/S3/Arith/Divisors/DivisorSubpower](../Divisors/DivisorSubpower.md)
- Dependency: [D5/S3/Arith/Robin/FibonacciRankEulerTail](../Robin/FibonacciRankEulerTail.md)
