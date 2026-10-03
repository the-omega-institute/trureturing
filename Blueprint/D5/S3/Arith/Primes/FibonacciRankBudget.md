# Complete Fibonacci Rank Budget

## Abstract

Finite rank-closed odd valuation support bounds the entire Fibonacci index.

**Theorem 1.1 (Every prime depth is bounded).**

Lean statement: `D5/S3/Arith/Primes/FibonacciRankBudget.fibonacci_rank_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciRankBudget.fibonacci_rank_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a finite set of primes containing two, three, and five. Assume that every prime factor of the first Fibonacci entry rank of a member of H also belongs to H, and let R be the least common multiple of those ranks. If every prime occurring to odd order in F_n belongs to H, for a positive index n, then n divides 5R. At every prime other than five the depth of n is at most its depth in R; at five one extra unit is allowed.

Support descent first places every index prime in H. An excessive depth e at a prime q at least seven produces an odd-order factor p of the nonsquare quotient F_(q^e)/F_(q^(e-1)). Its exact entry rank q^e excludes it from H and from the index. The original-rank valuation law preserves its odd order in F_n, contradicting the support condition. The two-, three-, and five-adic budgets supply the remaining cases.

The support assumption concerns odd valuations, so primes of even positive depth in F_n may lie outside H. The conclusion bounds indices for this fixed support set; it does not assert that every Fibonacci value has its prime support in a fixed finite set.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciRankBudget.fibonacci_rank_budget`
- Dependency: [D5/S3/Arith/Primes/FibonacciDyadicRankBudget](FibonacciDyadicRankBudget.md)
- Dependency: [D5/S3/Arith/Primes/FibonacciFiveAdicRankBudget](FibonacciFiveAdicRankBudget.md)
- Dependency: [D5/S3/Arith/Primes/FibonacciOddIndexNonsquare](FibonacciOddIndexNonsquare.md)
- Dependency: [D5/S3/Arith/Primes/FibonacciPrimePowerMod31Nonsquare](FibonacciPrimePowerMod31Nonsquare.md)
- Dependency: [D5/S3/Arith/Primes/FibonacciPrimePowerModularNonsquare](FibonacciPrimePowerModularNonsquare.md)
- Dependency: [D5/S3/Arith/Primes/FibonacciPrimeToIndexValuation](FibonacciPrimeToIndexValuation.md)
- Dependency: [D5/S3/Arith/Primes/FibonacciRecurrencePolynomialNonsquare](FibonacciRecurrencePolynomialNonsquare.md)
- Dependency: [D5/S3/Arith/Primes/FibonacciTernaryRankBudget](FibonacciTernaryRankBudget.md)
- Dependency: [D5/S3/Arith/Primes/OriginalOddDepthSupport](OriginalOddDepthSupport.md)
