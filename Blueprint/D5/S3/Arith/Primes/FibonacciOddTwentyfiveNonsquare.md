# Odd-Index Fibonacci Quotients Modulo Seven

## Abstract

Odd-index normalized twenty-five-fold Fibonacci quotients are nonsquares modulo seven.

**Theorem 1.1 (The normalized twenty-five-fold quotient).**

Lean statement: `D5/S3/Arith/Primes/FibonacciOddTwentyfiveNonsquare.fibonacci_odd_twentyfive_normalized_nonsquare`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciOddTwentyfiveNonsquare.fibonacci_odd_twentyfive_normalized_nonsquare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive odd index n, the Fibonacci number F_(25n) equals 25 times F_n times a natural number d. This d is five modulo seven and therefore is not a square. An eight-step sign change of the Fibonacci sequence modulo seven supplies the residue; the exact five-adic depth supplies the factor of twenty-five.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciOddTwentyfiveNonsquare.fibonacci_odd_twentyfive_normalized_nonsquare`
- Dependency: [D5/S3/Arith/Primes/FibonacciFiveAdicDepth](FibonacciFiveAdicDepth.md)
