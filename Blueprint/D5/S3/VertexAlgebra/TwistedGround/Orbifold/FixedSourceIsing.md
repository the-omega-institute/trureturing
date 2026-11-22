# Fixed-source Ising modes on the odd twisted sector

## Abstract

Fixed-source Ising modes on the odd twisted sector

Given hu : IsUnit D.G.det, the actual odd twisted sector is paritySpace D hu (-1).

**Theorem 1.1 (Fixed-source iterate).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.odd_iterate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.odd_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Borcherds law for two fixed sources gives the iterate on the actual odd twisted sector. The source of the iterated coefficient is formed with the fixed lattice mode.

**Theorem 1.2 (Fixed-source commutator).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.odd_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.odd_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same law expresses the commutator on the odd sector as a binomially weighted sum of modes of fixed lattice products.

**Definition 1.3 (Actual odd axis mode).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.oddAxisMode`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.oddAxisMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Virasoro mode L(m) is coefficient m + 1 of the fixed norm-four source on the negative parity slice.

**Theorem 1.4 (Virasoro action at central charge one half).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.odd_virasoro`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.odd_virasoro` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For norm four and a parameter s with s² = 1, the axis self-products truncate the commutator to four terms. Translation gives the derivative term and the odd vacuum coefficient gives (m³ − m)/24 when m + n = 0.

**Theorem 1.5 (Virasoro action on the fixed lattice subspace).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.fixed_virasoro`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.fixed_virasoro` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lattice Virasoro relation at central charge one half restricts to the fixed subspace for a norm-four charge and s² = 1.

**Theorem 1.6 (Virasoro action of the embedded axis).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.embedded_virasoro`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.embedded_virasoro` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the real Gram matrix D.G.map (Int.cast : ℤ → ℝ) is positive definite, ⟨a, a⟩ = 4, and s² = 1. Combining the fixed lattice and actual odd relations gives Virasoro for the literal embedded axis on the original two-sector carrier.

**Definition 1.7 (Level-six vacuum descendant).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.nullState`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.nullState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Form the vacuum descendant with coefficients 64, 93, −264 and −108 using the fixed lattice modes.

**Theorem 1.8 (Vanishing of the fixed vacuum descendant).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.fixed_vacuum_null`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.fixed_vacuum_null` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a norm-four charge and s² = 1, the lattice relation makes the level-six descendant zero in the fixed subspace.

**Theorem 1.9 (Vanishing of every odd null coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.odd_vacuum_null`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.odd_vacuum_null` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For ⟨a, a⟩ = 4 and s² = 1, the level-six vacuum descendant vanishes in the fixed lattice. Linearity in the fixed source then makes every coefficient of this descendant vanish on the odd twisted sector.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.embedded_virasoro`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.fixed_vacuum_null`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.fixed_virasoro`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.nullState`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.oddAxisMode`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.odd_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.odd_iterate`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.odd_vacuum_null`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing.odd_virasoro`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum](../../HalfFock/NormFourFirstGradeSpectrum.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourVacuumNull](../../Lattice/NormFourVacuumNull.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation](OriginalOrbifoldTranslation.md)
