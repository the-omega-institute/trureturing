# Golden Cubic Compatibility Density

## Abstract

The actual GCC4 unrestricted rational-prime compatibility event has positive Dirichlet density.

**Theorem 1.1 (Exact unrestricted rational-prime density).**

Lean statement: `D5/S3/Factorization/Galois/GoldenCubicCompatibilityDensity.actual_compatibility_density`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/GoldenCubicCompatibilityDensity.actual_compatibility_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each unit residue a modulo 80 times 3 to the power j plus 2 with image one modulo three, unrestricted rational primes in that class whose prime above E has the actual character-defined Frobenius have Dirichlet density two divided by the totient of the modulus and 3 to the power twice the earlier support size plus two. This density is positive.

The proof applies the cited general Chebotarev theorem to the computed two-element class, removes finite modulus and ramification exceptions, and identifies the prime-ideal Dirichlet series with the rational-prime series. Separately, there exists a unit residue b with positive representative that reduces to one modulo three and satisfies the oddness, quadratic-character and stated congruence conditions. Positive density among unrestricted primes does not assert a prime in the finite current block.

## References

- Truth anchor: `D5/S3/Factorization/Galois/GoldenCubicCompatibilityDensity.actual_compatibility_density`
- Dependency: [D5/S3/Factorization/Galois/GoldenCubicCompatibilityPrimeTransfer](GoldenCubicCompatibilityPrimeTransfer.md)
