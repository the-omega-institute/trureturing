# Golden Prime Period Bounds

## Abstract

Golden Frobenius gives prime residue-period bounds for the Fibonacci matrix.

**Theorem 1.1 (Split and inert period bounds).**

Lean statement: `D5/S3/Arith/GoldenPrimePeriodBounds.golden_prime_period_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenPrimePeriodBounds.golden_prime_period_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each prime greater than five, the Fibonacci matrix period divides p-1 when five is a quadratic residue modulo p, and divides 2(p+1) when it is a nonresidue. In either case the period is not divisible by p. The proof transports the Fibonacci entry-point congruence through the faithful golden multiplication representation.

## References

- Truth anchor: `D5/S3/Arith/GoldenPrimePeriodBounds.golden_prime_period_bounds`
- Dependency: [D5/S3/Arith/GoldenMatrixPeriodBridge](GoldenMatrixPeriodBridge.md)
