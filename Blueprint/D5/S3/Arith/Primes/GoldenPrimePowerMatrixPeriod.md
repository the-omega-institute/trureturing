# Prime-power Fibonacci matrix period

## Abstract

The Fibonacci matrix has an exact period at every power of a prime above five.

**Theorem 1.1 (Exact local period).**

Lean statement: `D5/S3/Arith/Primes/GoldenPrimePowerMatrixPeriod.golden_matrix_prime_power_period`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenPrimePowerMatrixPeriod.golden_matrix_prime_power_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be a prime greater than five, let a be positive, and let t be the order of the Fibonacci matrix modulo p. Let z be the first positive index with p dividing F_z, and let h be the p-adic valuation of F_z. The matrix order modulo p^a is exactly t times p raised to max(a-h,0). At the first return modulo p, F_t has p-adic valuation h, and F_(t-1)-1 also has valuation h. Cassini's identity relates those coordinates, and binomial expansion then raises the return depth by one for each additional factor p.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenPrimePowerMatrixPeriod.golden_matrix_prime_power_period`
- Dependency: [D5/S3/Arith/GoldenMatrixPeriodBridge](../GoldenMatrixPeriodBridge.md)
- Dependency: [D5/S3/Arith/GoldenPrimePeriodBounds](../GoldenPrimePeriodBounds.md)
- Dependency: [D5/S3/Arith/GoldenPrimePowerOrder](../GoldenPrimePowerOrder.md)
- Dependency: [D5/S3/Arith/Primes/FibonacciPrimeToIndexValuation](FibonacciPrimeToIndexValuation.md)
