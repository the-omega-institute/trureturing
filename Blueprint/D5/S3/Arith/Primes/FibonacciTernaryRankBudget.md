# Ternary Fibonacci rank budget

## Abstract

Odd Fibonacci support bounds the ternary depth of an index by ranks in its finite prime support.

**Theorem 1.1 (Ternary rank budget).**

Lean statement: `D5/S3/Arith/Primes/FibonacciTernaryRankBudget.fibonacci_ternary_rank_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciTernaryRankBudget.fibonacci_ternary_rank_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a finite set of primes containing two, and let R be the least common multiple of their first Fibonacci entry ranks. If every prime dividing a positive index n belongs to H and every prime occurring to odd order in F_n belongs to H, then the exponent of three in n is at most the exponent of three in R. At a larger exponent, a cubic Fibonacci block is two modulo five and yields an odd-order prime of exact rank 3^e. Its original valuation is transported to F_n through the prime-to-index theorem.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciTernaryRankBudget.fibonacci_ternary_rank_budget`
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockRanks](GoldenCubicBlockRanks.md)
