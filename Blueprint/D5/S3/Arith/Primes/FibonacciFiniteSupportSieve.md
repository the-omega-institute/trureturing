# Exact Finite Original-Depth Fibonacci Support Sieve

## Abstract

Exact Finite Original-Depth Fibonacci Support Sieve

**Theorem 1.1 (Exact Finite Original-Depth Fibonacci Support Sieve).**

Lean statement: `D5/S3/Arith/Primes/FibonacciFiniteSupportSieve.fibonacci_finite_support_sieve`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciFiniteSupportSieve.fibonacci_finite_support_sieve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite set S of primes greater than five. Let H be its least Fibonacci rank closure and R the least common multiple of the entry ranks of the members of H. For n define D(n) as the product, over H, of p to the valuation of F_n at p, and let Z(n)=F_n/D(n).

The positive indices with external odd original-depth support U(n) contained in S are exactly the divisors of 5R for which the integer square root of Z(n) squares back to Z(n) and every qualifying prime in H belongs to S. Here qualifying means prime p greater than five dividing F_n, not dividing n, with odd original entry-rank depth.

The positive indices with F_n powerful and original odd-super-depth support T(n) contained in S are exactly the divisors of 5R for which Z(n) passes the same square test, no prime in H dividing F_n has valuation one, and each prime in H greater than five dividing F_n with odd original depth at least three belongs to S.

The quotient removes all powers of primes in H. Its factorization is zero on H and agrees with that of F_n elsewhere. Even exponents outside H give an explicit square root, and a square root forces those exponents to be even. The index cutoff and closure ensure that outside primes do not divide n, so their valuations are the original entry-rank depths. The supported powerful indices therefore form a finite set with cardinality at most the minimum of two to the size of H minus four and the number of divisors of 5R. The checks use known ranks and valuations in H and a residual integer square root; they do not require a complete factorization of each large Fibonacci value or assert a polynomial time bound.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciFiniteSupportSieve.fibonacci_finite_support_sieve`
- Dependency: [D5/S3/Arith/Primes/FibonacciPrimeToIndexValuation](FibonacciPrimeToIndexValuation.md)
- Dependency: [D5/S3/Arith/Primes/FibonacciRankBudget](FibonacciRankBudget.md)
- Dependency: [D5/S3/Arith/Primes/PowerfulFibonacciSupportBound](PowerfulFibonacciSupportBound.md)
