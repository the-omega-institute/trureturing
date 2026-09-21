# Mixed Prime History Generating Polynomials

## Abstract

Mixed Prime History Generating Polynomials.

**Theorem 1.1 (Coefficients count histories of a fixed length).**

Lean statement: `D5/S3/Factorization/Combinatorics/MixedPrimeHistoryGenerating.mixed_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/MixedPrimeHistoryGenerating.mixed_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start with the polynomial z. At each step, sum over primes q at most J, adding both z to the power q times the previous polynomial and the previous polynomial evaluated at z to the power q. Retain exactly degrees one through J. For every natural length k and every n between one and J, the coefficient of degree n in the kth iterate is the number of typed prime histories of length k ending at n. Addition and multiplication contribute separately, including when they lead to the same endpoint.

**Theorem 1.2 (The endpoint bounds the history length).**

Lean statement: `D5/S3/Factorization/Combinatorics/MixedPrimeHistoryGenerating.sharp_length_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/MixedPrimeHistoryGenerating.sharp_length_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonempty typed prime history starts at one and ends at an integer at least twice its length. The first letter reaches at least two. Every subsequent addition increases the state by a prime at least two, while multiplication by a prime increases a state at least two by at least two. Consequently, a history ending at n has length at most the integer part of n divided by two.

## References

- Truth anchor: `D5/S3/Factorization/Combinatorics/MixedPrimeHistoryGenerating.mixed_coefficient`
- Truth anchor: `D5/S3/Factorization/Combinatorics/MixedPrimeHistoryGenerating.sharp_length_bound`
- Dependency: [D5/S3/Factorization/Combinatorics/MixedPrimeHistoryCount](MixedPrimeHistoryCount.md)
