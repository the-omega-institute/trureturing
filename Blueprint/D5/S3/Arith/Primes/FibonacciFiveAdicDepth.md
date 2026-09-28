# Five-adic Fibonacci depth

## Abstract

For every positive index, the five-adic Fibonacci depth equals the index depth.

**Theorem 1.1 (Exact five-adic depth).**

Lean statement: `D5/S3/Arith/Primes/FibonacciFiveAdicDepth.fibonacci_five_adic_depth`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciFiveAdicDepth.fibonacci_five_adic_depth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive n, the exponent of five in F_n equals the exponent of five in n. The proof computes the fifth power of the golden integer phi^n: its Fibonacci coordinate gains one factor of five, while the remaining factor is a unit modulo five by the norm equation. The Fibonacci entry point at five starts the induction.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciFiveAdicDepth.fibonacci_five_adic_depth`
