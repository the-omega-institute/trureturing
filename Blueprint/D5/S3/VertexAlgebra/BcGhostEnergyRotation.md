# Actual bc ghost conformal-energy half-turn

## Abstract

The full finite-support bc Fock carrier has a real integer conformal-energy half-turn.

For a finite-support ghost state indexed by a finite subset S of the actual mode sites, use the native integer siteWeight and energy(S) = sum siteWeight. The operator rotation is the diagonal finite-support linear operator with coefficient (-1)^energy(S), where the exponent is the integer zpow and may be negative.

**Theorem 1.1 (Energy rotation is an involution).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostEnergyRotation.rotation_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostEnergyRotation.rotation_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal phase squares to one on every actual basis state, so rotation composed with itself is the identity on the unrestricted algebraic Fock carrier.

**Theorem 1.2 (Energy rotation has real coefficients).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostEnergyRotation.rotation_star_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostEnergyRotation.rotation_star_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complex conjugation fixes every integer power of -1, giving coefficientwise compatibility with the native conjugate-left convention.

**Theorem 1.3 (Energy rotation commutes with the actual ghost L(0)).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostEnergyRotation.rotation_commutes_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostEnergyRotation.rotation_commutes_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The operator is diagonal in the same unrestricted finite-subset basis as the actual L(0), whose eigenvalue is the native integer energy.

**Theorem 1.4 (Energy rotation intertwines every b mode).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostEnergyRotation.rotation_b`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostEnergyRotation.rotation_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual b mode changes the native ghost energy by -mode, including both creator and annihilator branches, so rotation passes through b(mode) with phase (-1)^mode.

**Theorem 1.5 (Energy rotation intertwines every c mode).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostEnergyRotation.rotation_c`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostEnergyRotation.rotation_c` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual c mode has the same energy-shift phase law on both creation and annihilation branches; negative integer energies use the genuine integer zpow.

This document does not assert the matter oscillator pairing, inverse-Gram Sugawara adjoint, individual A(n) correction, finite symmetric Q cancellation, boundary-cycle orthogonality, quotient descent, charged PCT, or physical no-ghost/isometry conclusions.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BcGhostEnergyRotation.rotation_b`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostEnergyRotation.rotation_c`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostEnergyRotation.rotation_commutes_zero`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostEnergyRotation.rotation_involutive`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostEnergyRotation.rotation_star_coefficient`
