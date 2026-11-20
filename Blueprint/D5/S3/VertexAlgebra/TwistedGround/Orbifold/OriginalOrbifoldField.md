# The Original Two-Sector Orbifold Field

## Abstract

The Original Two-Sector Orbifold Field

**Definition 1.1 (State space).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Carrier`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Carrier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The state space is the product of the fixed lattice sector and the negative twisted parity sector.

**Definition 1.2 (Vacuum state).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.vacuumState`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.vacuumState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vacuum is the fixed lattice vacuum paired with the zero twisted state.

**Definition 1.3 (Four mode blocks).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.mode`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.mode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mode combines the fixed lattice field, the fixed-action parity slice, the original right coefficient, and the original inverse-pairing coefficient.

**Theorem 1.4 (Lower truncation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.mode_tail`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.mode_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each pair of states, all integer modes at and above a common bound vanish. The bound combines the field tails and the grade bound of the inverse-pairing coefficient.

**Definition 1.5 (Assembled field).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use lower truncation to assemble the modes into a vertex operator that is complex-linear in its source state.

**Theorem 1.6 (Normalized coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_ncoeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_ncoeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized coefficient of the assembled field is the corresponding mode.

**Theorem 1.7 (Mode on two states).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_ncoeff_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_ncoeff_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed and inverse-pairing terms sum in the fixed sector. The parity-slice and original right-field terms sum in the twisted sector.

**Theorem 1.8 (Fixed source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_fixed_ncoeff_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_fixed_ncoeff_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each mode of a fixed source acts on the fixed sector by the lattice mode and on the twisted sector by the parity slice.

**Theorem 1.9 (Borcherds identity on the negative sector).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.fixedParitySlice_borcherds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.fixedParitySlice_borcherds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two fixed inputs and any negative twisted input, all three signed coefficient families have finite support. The native transport law yields the Borcherds equality for all three integer indices.

**Theorem 1.10 (Borcherds identity for the assembled field).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_borcherds_vvm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_borcherds_vvm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two fixed states and one negative twisted state, the parity inclusion carries the three finite coefficient families and their signed Borcherds equality into the assembled carrier.

**Theorem 1.11 (Negative twisted source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_twisted_ncoeff_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_twisted_ncoeff_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A twisted source exchanges sectors through the inverse-pairing coefficient and the original right coefficient.

**Theorem 1.12 (Vacuum modes).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.vacuum_ncoeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.vacuum_ncoeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vacuum field acts as the identity at mode minus one and vanishes at every other integer mode.

**Theorem 1.13 (Creation and regularity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.creation_ncoeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.creation_ncoeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Acting on the vacuum, mode minus one returns the source state and every higher mode vanishes. In the twisted part, the original right sum reduces to its zeroth term.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Carrier`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_borcherds_vvm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_fixed_ncoeff_apply`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_ncoeff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_ncoeff_apply`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_twisted_ncoeff_apply`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.creation_ncoeff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.fixedParitySlice_borcherds`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.mode`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.mode_tail`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.vacuumState`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.vacuum_ncoeff`
- Dependency: [D5/S3/VertexAlgebra/GroundRightCurrentTransport/FirstSourceClosure](../../GroundRightCurrentTransport/FirstSourceClosure.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherds](../../LatticeHalfFockCurrentBorcherds.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients](../OriginalFourMCoefficients.md)
