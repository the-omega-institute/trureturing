# Odd-Index Fibonacci Nonsquares

## Abstract

A Lucas modulus supplies a quadratic obstruction for every nontrivial odd Fibonacci index.

**Theorem 1.1 (Every odd index at least three is excluded).**

Lean statement: `D5/S3/Arith/Primes/FibonacciOddIndexNonsquare.fibonacci_odd_index_nonsquare`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciOddIndexNonsquare.fibonacci_odd_index_nonsquare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every odd natural number m at least three, F_m is not a square. Write m as 4t plus or minus one and factor t as 2^r times an odd s. The Lucas modulus L_(2^(r+1)) is positive and is three modulo four.

In the golden integer ring, the trace and norm of phi^(2^(r+1)) give phi^(2^(r+2)) equal to minus one modulo this modulus. The odd factor s preserves that sign. The golden coordinate in the plus case, or the constant coordinate after multiplication by phi in the minus case, gives F_m equal to minus one modulo the same Lucas number.

The Jacobi symbol of minus one is minus one for a modulus equal to three modulo four. Therefore F_m cannot be a square. This applies to initial odd prime indices; it does not assert a classification of squares at even indices or a nonsquare criterion for arbitrary ratios of Fibonacci numbers.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciOddIndexNonsquare.fibonacci_odd_index_nonsquare`
