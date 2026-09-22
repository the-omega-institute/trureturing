# Mixed Prime Histories Ending at Primes

## Abstract

Mixed Prime Histories Ending at Primes.

**Theorem 1.1 (Counting histories with prime endpoints).**

Lean statement: `D5/S3/Factorization/Combinatorics/MixedPrimeHistoryPrimeEndpointBound.prime_endpoint_count_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/MixedPrimeHistoryPrimeEndpointBound.prime_endpoint_count_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X and k be natural numbers at least two, and let m count the primes at most X. The number of typed additive and multiplicative prime histories of length k ending at these primes is at most m times (2m) to the power k minus one. Every label uses a prime at most X. The final letter must be additive, since a multiplication after a nonempty prefix would produce a composite endpoint. The endpoint and the first k minus one labels therefore determine the final label uniquely. There are m choices for the endpoint and at most 2m choices for each prefix label.

## References

- Truth anchor: `D5/S3/Factorization/Combinatorics/MixedPrimeHistoryPrimeEndpointBound.prime_endpoint_count_bound`
- Dependency: [D5/S3/Factorization/Combinatorics/MixedPrimeHistoryCount](MixedPrimeHistoryCount.md)
- Dependency: [D5/S3/Factorization/Combinatorics/MixedPrimeHistoryGenerating](MixedPrimeHistoryGenerating.md)
