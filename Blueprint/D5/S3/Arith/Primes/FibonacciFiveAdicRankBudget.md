# Five-Adic Fibonacci Rank Budget

## Abstract

Odd Fibonacci support bounds five-adic index depth by the rank budget plus one.

**Theorem 1.1 (Five-adic rank budget).**

Lean statement: `D5/S3/Arith/Primes/FibonacciFiveAdicRankBudget.fibonacci_five_adic_rank_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciFiveAdicRankBudget.fibonacci_five_adic_rank_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a finite set of primes, and let R be the least common multiple of their first Fibonacci entry ranks. If every prime dividing an index n belongs to H and every prime occurring to odd order in F_n belongs to H, then the exponent of five in n is at most one more than the exponent of five in R. A nonsquare normalized quotient at the odd index 5^a has an odd-order prime whose entry rank exceeds 5^a. The prime-to-index valuation law carries that odd order to F_n, contradicting the support assumption when the index is too deep.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciFiveAdicRankBudget.fibonacci_five_adic_rank_budget`
- Dependency: [D5/S3/Arith/Primes/FibonacciOddTwentyfiveNonsquare](FibonacciOddTwentyfiveNonsquare.md)
- Dependency: [D5/S3/Arith/Primes/FibonacciPrimeToIndexValuation](FibonacciPrimeToIndexValuation.md)
