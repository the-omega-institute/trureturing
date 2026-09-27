# Golden Fibonacci Modulus Period

## Abstract

Odd Fibonacci values carry an exact fourfold return of the Fibonacci matrix.

**Theorem 1.1 (Exact period at an odd Fibonacci modulus).**

Lean statement: `D5/S3/Arith/GoldenFibonacciModulusPeriod.golden_fibonacci_modulus_period`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenFibonacciModulusPeriod.golden_fibonacci_modulus_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every odd index n at least five, the Fibonacci matrix modulo F_n has multiplicative order exactly 4n. A matrix return forces F_n to divide the Fibonacci number at the return index. Strong divisibility and strict growth then force n to divide that index. At the nth power the matrix is scalar, and Cassini's identity makes that scalar's square equal to minus one. Since F_n is greater than two, its scalar has order four, excluding every shorter return.

## References

- Truth anchor: `D5/S3/Arith/GoldenFibonacciModulusPeriod.golden_fibonacci_modulus_period`
- Dependency: [D5/S3/Arith/GoldenMatrixPeriodBridge](GoldenMatrixPeriodBridge.md)
