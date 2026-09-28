# Prime-power Fibonacci matrix period

## Abstract

The Fibonacci matrix has an exact period at every power of a prime above five.

**Theorem 1.1 (Exact local period).**

Lean statement: `D5/S3/Arith/Primes/GoldenPrimePowerMatrixPeriod.golden_matrix_prime_power_period`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenPrimePowerMatrixPeriod.golden_matrix_prime_power_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be a prime greater than five, let a be positive, and let t be the order of the Fibonacci matrix modulo p. Let z be the first positive index with p dividing F_z, and let h be the p-adic valuation of F_z. The matrix order modulo p^a is exactly t times p raised to max(a-h,0). At the first return modulo p, F_t has p-adic valuation h, and F_(t-1)-1 also has valuation h. The period t is even. Cassini's factorization gives (F_(t-1)-1)(F_(t-1)+1)=F_t(F_t-F_(t-1)), with both F_(t-1)+1 and F_t-F_(t-1) prime to p. The coordinates have the forms F_(t-1)=1+p^h u and F_t=p^h v, where p does not divide v. The natural-number matrix A=((u+v,v),(v,u)) is nonzero modulo p and satisfies Q^t=I+p^h A at every natural modulus q. For every positive m, the t*m-th power is the identity modulo p^a exactly when a is at most h plus the p-adic valuation of m; every return exponent modulo p^a is divisible by t.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenPrimePowerMatrixPeriod.golden_matrix_prime_power_period`
- Dependency: [D5/S3/Arith/GoldenMatrixPeriodBridge](../GoldenMatrixPeriodBridge.md)
- Dependency: [D5/S3/Arith/GoldenPrimePeriodBounds](../GoldenPrimePeriodBounds.md)
- Dependency: [D5/S3/Arith/GoldenPrimePowerOrder](../GoldenPrimePowerOrder.md)
- Dependency: [D5/S3/Arith/Primes/FibonacciPrimeToIndexValuation](FibonacciPrimeToIndexValuation.md)
