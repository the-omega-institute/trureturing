# Prime-Support Initial Segment

## Abstract

Minimal odd distinct covers have an initial segment of odd prime support.

**Theorem 1.1 (The common modulus contains the smaller odd-prime product).**

Lean statement: `D5/S3/Arith/Covering/PrimeSupportInitialSegment.odd_prime_product_dvd_commonModulus`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/PrimeSupportInitialSegment.odd_prime_product_dvd_commonModulus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a distinct odd covering system that is minimal first in its number of classes and then in the sum of its moduli. If a prime q divides the common modulus, then the product of every odd prime below q also divides that common modulus.

The proof applies the prime-support gap descent to each smaller odd prime and then combines the resulting pairwise-coprime divisibilities by finite induction. This records a support prefix for a minimal counterexample; it does not prove that an unrestricted odd covering system cannot exist.

## References

- Truth anchor: `D5/S3/Arith/Covering/PrimeSupportInitialSegment.odd_prime_product_dvd_commonModulus`
- Dependency: [D5/S3/Arith/Covering/PrimeSupportGapDescent](PrimeSupportGapDescent.md)
