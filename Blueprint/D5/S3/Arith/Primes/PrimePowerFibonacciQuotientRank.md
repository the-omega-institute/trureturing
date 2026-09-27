# Prime-Power Fibonacci Quotient Rank

## Abstract

Consecutive prime-power Fibonacci indices have fresh prime support.

**Theorem 1.1 (First-entry rank of quotient prime factors).**

Lean statement: `D5/S3/Arith/Primes/PrimePowerFibonacciQuotientRank.prime_power_fibonacci_quotient_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/PrimePowerFibonacciQuotientRank.prime_power_fibonacci_quotient_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be a prime greater than five. The quotient of F_(p^(k+1)) by F_(p^k) exceeds one for every k at least zero. Every prime dividing this quotient has first Fibonacci zero index exactly p^(k+1). The proof first excludes p from F_(p^(k+1)) using the prime rank bound. Any other prime with an earlier rank would divide both Fibonacci values. Its prime-to-index valuations would then be equal, contradicting its additional occurrence in the quotient.

## References

- Truth anchor: `D5/S3/Arith/Primes/PrimePowerFibonacciQuotientRank.prime_power_fibonacci_quotient_rank`
- Dependency: [D5/S3/Arith/Primes/FibonacciPrimeToIndexValuation](FibonacciPrimeToIndexValuation.md)
