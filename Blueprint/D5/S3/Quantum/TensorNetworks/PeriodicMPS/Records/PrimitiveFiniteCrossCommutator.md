# Finite-ring cross commutation for the primitive periodic collision

## Abstract

Finite-ring cross commutation for the primitive periodic collision.

**Definition 1.1 (The fixed visible commutator matrix).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveFiniteCrossCommutator.collisionCommutatorMatrix`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveFiniteCrossCommutator.collisionCommutatorMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

In visible order 00, 01, 10, 11, the four rows of K are (1,0,0,1), (0,−1,−1,0), (0,−1,−1,0) and (1,0,0,1).

**Theorem 1.2 (Exact commutator of the finite cross reduction).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveFiniteCrossCommutator.collision_flattening_cross_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveFiniteCrossCommutator.collision_flattening_cross_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every m ≥ 0, put n = m + 2 and let Wᵦ be the normalized amplitude flattening for label b, with the first two sites indexing its rows. The literal 4 by 4 cross reduction is Sₙ = W₀W₁†. With R = collisionMarginal, RSₙ − SₙR = 12((−8)ᵐ + (8i)ᵐ)/(√200)ⁿ times K. The matrix R is the common two-site density for m ≥ 5.

**Theorem 1.3 (Commutation exactly at ring lengths divisible by four).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveFiniteCrossCommutator.collision_flattening_cross_commute_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveFiniteCrossCommutator.collision_flattening_cross_commute_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every m ≥ 0, R commutes with W₀W₁† exactly when (m + 2) mod 4 = 0. The fixed matrix K has a unit entry and the scalar vanishes exactly when m mod 4 = 2.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveFiniteCrossCommutator.collisionCommutatorMatrix`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveFiniteCrossCommutator.collision_flattening_cross_commutator`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveFiniteCrossCommutator.collision_flattening_cross_commute_iff`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient](PrimitiveRecordLeadingCoefficient.md)
