# Chebyshev Factorial Ratio Divisibility by 3n+1

## Abstract

Chebyshev Factorial Ratio Divisibility by 3n+1.

**Theorem 1.1 (Divisibility at every natural index).**

Lean statement: `D5/S3/Arith/FactorialRatio/BalaChebyshevThreeDivisibility.bala_three_integrality`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/BalaChebyshevThreeDivisibility.bala_three_integrality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural number n, including zero, the factorial ratio (30n)!n!/((3n+1)(15n)!(10n)!(6n)!) is an integer: (3n+1)(15n)!(10n)!(6n)! divides (30n)!n!. No primality or other additional hypothesis on n is required. Legendre's formula reduces the result to prime valuations. The local floor defect is nonnegative for every positive modulus, and it equals one when the modulus divides 3n+1 and is seven or at least ten. The exceptional primes two and five are handled by binomial valuations; three never divides 3n+1.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaChebyshevThreeDivisibility.bala_three_integrality`
