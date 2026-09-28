# Dyadic Fibonacci rank budget

## Abstract

Odd Fibonacci support bounds the dyadic depth of an index by the ranks in its finite prime support.

**Theorem 1.1 (Dyadic rank budget).**

Lean statement: `D5/S3/Arith/Primes/FibonacciDyadicRankBudget.fibonacci_dyadic_rank_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciDyadicRankBudget.fibonacci_dyadic_rank_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a finite set of primes containing three, and let R be the least common multiple of their first Fibonacci entry ranks. If every prime dividing a positive index n belongs to H and every prime occurring to odd order in F_n belongs to H, then the exponent of two in n is at most the exponent of two in R. A nonsquare dyadic Fibonacci quotient yields an odd-order prime at the first rank 2^e; its valuation is transported to F_n using the prime-to-index valuation theorem.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciDyadicRankBudget.fibonacci_dyadic_rank_budget`
- Dependency: [D5/S3/Arith/Primes/FibonacciDyadicQuotientNonsquare](FibonacciDyadicQuotientNonsquare.md)
- Dependency: [D5/S3/Arith/Primes/FibonacciPrimeToIndexValuation](FibonacciPrimeToIndexValuation.md)
