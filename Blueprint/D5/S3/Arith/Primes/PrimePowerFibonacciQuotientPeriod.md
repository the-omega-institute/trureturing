# Prime-Power Fibonacci Quotient Period

## Abstract

Fresh prime factors of prime-power Fibonacci quotients have exact matrix periods.

**Theorem 1.1 (Exact fourfold period of a fresh prime factor).**

Lean statement: `D5/S3/Arith/Primes/PrimePowerFibonacciQuotientPeriod.prime_power_fibonacci_quotient_period`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/PrimePowerFibonacciQuotientPeriod.prime_power_fibonacci_quotient_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be a prime greater than five and let q be any prime factor of F_(p^(k+1))/F_(p^k). The Fibonacci matrix modulo q has multiplicative order exactly 4p^(k+1). Its first zero index is p^(k+1), so every return time is a multiple of that index. Cassini's identity makes the matrix at that index square to minus one, excluding the shorter returns while its fourth power is one.

## References

- Truth anchor: `D5/S3/Arith/Primes/PrimePowerFibonacciQuotientPeriod.prime_power_fibonacci_quotient_period`
- Dependency: [D5/S3/Arith/GoldenMatrixPeriodBridge](../GoldenMatrixPeriodBridge.md)
- Dependency: [D5/S3/Arith/Primes/PrimePowerFibonacciQuotientRank](PrimePowerFibonacciQuotientRank.md)
