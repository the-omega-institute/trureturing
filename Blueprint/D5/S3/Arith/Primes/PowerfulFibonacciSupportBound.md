# Powerful Fibonacci support bound

## Abstract

A finite original odd-depth support bounds powerful Fibonacci indices under explicit classical inputs.

Fix a finite set S of primes greater than five and its least Fibonacci rank closure H(S). This theorem assumes the prime-index odd-factor input, the classification of powerful Fibonacci values with five-smooth indices, and uniqueness of the remaining Fibonacci square classes for all positive indices. These three results remain explicit premises in the Lean statement; prime-to-index valuation is proved.

**Definition 1.1 (Odd prime support).**

Lean statement: `D5/S3/Arith/Primes/PowerfulFibonacciSupportBound.oddPrimeSupport`

*Formalization.* `D5/S3/Arith/Primes/PowerfulFibonacciSupportBound.oddPrimeSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The distinct prime factors of the original Fibonacci value F_n whose valuations in F_n are odd.

**Definition 1.2 (Supported powerful index).**

Lean statement: `D5/S3/Arith/Primes/PowerfulFibonacciSupportBound.supportedPowerfulIndex`

*Formalization.* `D5/S3/Arith/Primes/PowerfulFibonacciSupportBound.supportedPowerfulIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A positive index n belongs when F_n is powerful and every prime factor of F_n with odd original depth at least three belongs to S. The condition uses the first Fibonacci zero rank of each prime, not the depth at a multiplied index.

**Theorem 1.3 (Finite count with four exceptions).**

Lean statement: `D5/S3/Arith/Primes/PowerfulFibonacciSupportBound.powerful_fibonacci_support_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/PowerfulFibonacciSupportBound.powerful_fibonacci_support_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the three stated premises, there is a finite set containing exactly the supported powerful indices, with cardinality at most two to the size of H(S) minus four. The proof places every odd prime support inside H(S), uses the index-support descent to reduce small odd support to five-smooth indices, and injects all remaining indices into the subsets of H(S) outside the eight small supports. The small group contributes at most four indices.

## References

- Truth anchor: `D5/S3/Arith/Primes/PowerfulFibonacciSupportBound.oddPrimeSupport`
- Truth anchor: `D5/S3/Arith/Primes/PowerfulFibonacciSupportBound.powerful_fibonacci_support_bound`
- Truth anchor: `D5/S3/Arith/Primes/PowerfulFibonacciSupportBound.supportedPowerfulIndex`
- Dependency: [D5/S3/Arith/Powerful/PowerfulNumber](../Powerful/PowerfulNumber.md)
- Dependency: [D5/S3/Arith/Primes/OriginalOddDepthSupport](OriginalOddDepthSupport.md)
