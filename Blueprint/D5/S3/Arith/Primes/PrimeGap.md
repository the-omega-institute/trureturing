# Gaps between consecutive primes

## Abstract

The gap after the n-th prime is positive, and the factorial construction makes it exceed any prescribed bound.

Indexing the primes in increasing order gives a gap function on the naturals. Positivity records that consecutive primes are distinct; unboundedness is the classical consequence of the fact that a factorial is divisible by every small number, which produces an interval containing no prime at all.

**Definition 1.1 (The gap function).**

Lean statement: `D5/S3/Arith/Primes/PrimeGap.primeGap`

*Formalization.* `D5/S3/Arith/Primes/PrimeGap.primeGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural number n, primeGap n is the difference between the prime of index n plus one and the prime of index n, where the primes are enumerated in increasing order starting from two at index zero.

**Theorem 1.2 (Positivity).**

Lean statement: `D5/S3/Arith/Primes/PrimeGap.primeGap_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/PrimeGap.primeGap_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every gap is positive. The primes form an infinite set of naturals, so their increasing enumeration is strictly monotone, and the difference of a term from its successor is a difference of a strictly smaller natural from a larger one.

**Theorem 1.3 (Gaps exceed every bound).**

Lean statement: `D5/S3/Arith/Primes/PrimeGap.exists_primeGap_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/PrimeGap.exists_primeGap_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural number N there is an index whose gap is at least N. Put m equal to N plus two. Each of the m minus one consecutive integers from the factorial of m plus two up to the factorial of m plus m is composite, because the offset divides the factorial and divides itself, while the sum exceeds the offset. That interval therefore contains no prime. Taking the first index whose prime exceeds the factorial of m plus one, the prime at the preceding index lies below that threshold and the prime at that index lies above the whole interval, so the gap at the preceding index is at least m minus one, which is at least N. The classical factorial construction is carried out here rather than taken from an existing statement of the same conclusion.

## References

- Truth anchor: `D5/S3/Arith/Primes/PrimeGap.exists_primeGap_ge`
- Truth anchor: `D5/S3/Arith/Primes/PrimeGap.primeGap`
- Truth anchor: `D5/S3/Arith/Primes/PrimeGap.primeGap_pos`
