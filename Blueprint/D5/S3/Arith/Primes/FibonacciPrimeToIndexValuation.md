# Prime-to-index Fibonacci valuation

## Abstract

At a prime absent from the index, Fibonacci valuation equals the depth at its first zero.

Let p be prime and p divide F_n while p does not divide n. Its original entry rank is the least positive r for which p divides F_r.

**Theorem 1.1 (Original rank valuation).**

Lean statement: `D5/S3/Arith/Primes/FibonacciPrimeToIndexValuation.fibonacci_original_rank_valuation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciPrimeToIndexValuation.fibonacci_original_rank_valuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The p-adic valuations of F_n and F_r agree. The proof factors the golden-power Fibonacci coordinate into F_r and an integral quotient. Modulo p that quotient is the index multiplier times a power of the adjacent Fibonacci coordinate, so p does not divide it when p divides neither the multiplier nor that adjacent coordinate.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciPrimeToIndexValuation.fibonacci_original_rank_valuation`
- Dependency: [D5/S0/Carrier/Ring](../../../S0/Carrier/Ring.md)
- Dependency: [D5/S3/Arith/Primes/FiniteFibonacciRankClosure](FiniteFibonacciRankClosure.md)
