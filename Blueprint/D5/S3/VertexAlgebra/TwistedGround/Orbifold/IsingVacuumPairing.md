# The original Ising mode-three vacuum channels

## Abstract

The original Ising mode-three vacuum channels

The input space is the whole negative twisted carrier at physical energy two for a rank-24 lattice with unit Gram determinant. The axis is the actual fixed state of a charge of norm four with sign s satisfying s² = 1. The vacuum pairing results below assume that the real Gram matrix is positive definite. These hypotheses include both signs in each of the 24 Leech frame directions.

**Theorem 1.1 (Positive modes on physical energy two).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingVacuumPairing.oddAxisMode_pos_eq_zero_energyTwo`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingVacuumPairing.oddAxisMode_pos_eq_zero_energyTwo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive integer Ising mode kills this full grade. The source has energy two and the raw doubled index for axis mode k is −2(k+1)−2. The corresponding signed oscillator output grade is 1−2k.

**Theorem 1.2 (The mode-three pairing).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingVacuumPairing.originalI_three_energyTwo`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingVacuumPairing.originalI_three_energyTwo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original two-twisted mode three on physical energy-two inputs u and v is the fixed vacuum times the ordered scalar actualForm(v,u). The original inverse of the source pairing realizes the output on grade zero.

**Theorem 1.3 (Vanishing for distinct axis weights).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingVacuumPairing.originalI_three_offDiagonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingVacuumPairing.originalI_three_offDiagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For unequal axis weights among 0, 1/2 and 1/16, the actual mode-three product is zero. The fixed lattice pairing with the vacuum is a dual primary of weight zero. On a fixed input of grade n, the axis mode k changes the grade to n−k. For k ≤ 0, only n = k = 0 can contribute to the vacuum pairing, and creation kills that term. The original primary selection law forces equality of the two input weights whenever the vacuum coefficient is nonzero.

**Theorem 1.4 (Nondegeneracy in each axis eigenspace).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingVacuumPairing.vacuumPairing_nondegenerate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingVacuumPairing.vacuumPairing_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordered pairing has zero left and right radicals on each of the three literal axis eigenspaces. Ambient nondegeneracy and orthogonality of different oscillator grades first give zero radical on the full physical grade. The three actual grade-one projectors decompose every test vector. The unequal-weight pairings vanish, so a block radical vector is in the full radical.

**Theorem 1.5 (A normalized partner in the same eigenspace).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingVacuumPairing.exists_sameWeight_vacuum_partner`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingVacuumPairing.exists_sameWeight_vacuum_partner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each nonzero input, nondegeneracy supplies a partner of the same weight with a nonzero ordered pairing. Scaling that partner by the inverse pairing gives the actual fixed vacuum under mode three of the assembled orbifold field.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingVacuumPairing.exists_sameWeight_vacuum_partner`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingVacuumPairing.oddAxisMode_pos_eq_zero_energyTwo`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingVacuumPairing.originalI_three_energyTwo`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingVacuumPairing.originalI_three_offDiagonal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingVacuumPairing.vacuumPairing_nondegenerate`
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourCosetVirasoro](../../Lattice/NormFourCosetVirasoro.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingPrimaryCoupling](IsingPrimaryCoupling.md)
