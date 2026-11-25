# Quartic compact factorial gcd

## Abstract

Quadratic logarithmic gap

**Theorem 1.1 (Quadratic logarithmic gap).**

Lean statement: `D5/S3/Arith/FactorialRatio/QuarticCompactLog.quartic_compact_log_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/QuarticCompactLog.quartic_compact_log_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write the logarithmic gap as the logarithm of the integral quotient of the compact gcd by the tail LCM. Expand it as a sum of exponent differences weighted by log p. The small primes contribute at most 3(log 4+4)r^2 by the Chebyshev psi bound. Finite summation by parts bounds the sum of log p divided by sqrt(p) up to s by 2(log 4+4)sqrt(s). Since s<r^2, the large primes contribute at most 8(log 4+4)r^2.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/QuarticCompactLog.quartic_compact_log_gap`
- Dependency: [D5/S3/Arith/FactorialRatio/QuarticPrimeWitness](QuarticPrimeWitness.md)
