# Three-Ring Profile Factorisation Modulo Sixty

## Abstract

The prime three-ring profile factors uniquely through units modulo sixty.

**Definition 1.1 (The splitting profile of a prime coprime to sixty).**

$$\left(\Sigma_{3}\right)\left(p\right) = g\left(p \bmod 60\right)$$

*Formalization.* `D5/S3/PrimeForms/Splitting/ThreeRingProfileFactorization.primeThreeRingProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a prime unramified at two, three, and five, the three-ring profile is the canonical unit-class image evaluated at the prime's residue modulo sixty. The already-factored map on units is reused rather than redefined.

**Theorem 1.2 (The profile depends only on the residue modulo sixty).**

$$\forall p, \left(\Sigma_{3}\right)\left(p\right) = g\left(p \bmod 60\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/ThreeRingProfileFactorization.prime_three_ring_profile_factors_mod_sixty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two primes with the same residue modulo sixty carry the same three-ring splitting profile, so the profile factors through the unit group of the integers modulo sixty.

**Theorem 1.3 (The factoring map is unique).**

$$\exists! f, \forall p, \left(\Sigma_{3}\right)\left(p\right) = f\left(p \bmod 60\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/ThreeRingProfileFactorization.prime_three_ring_profile_factor_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exactly one map on units modulo sixty factors the three-ring profile of every prime coprime to sixty.

Uniqueness needs each unit class to contain a prime, which Dirichlet's theorem on primes in arithmetic progressions supplies from pinned mathlib.

## References

- Truth anchor: `D5/S3/PrimeForms/Splitting/ThreeRingProfileFactorization.primeThreeRingProfile`
- Truth anchor: `D5/S3/PrimeForms/Splitting/ThreeRingProfileFactorization.prime_three_ring_profile_factor_unique`
- Truth anchor: `D5/S3/PrimeForms/Splitting/ThreeRingProfileFactorization.prime_three_ring_profile_factors_mod_sixty`
- Dependency: [D5/S3/PrimeForms/Splitting/ThreeRingProfileFibers](ThreeRingProfileFibers.md)
