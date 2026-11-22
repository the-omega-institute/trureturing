# Projection Onto the Actual Fixed Space

## Abstract

The complex-linear projection for the lattice sign involution.

The lattice data consist of a natural-number rank and a symmetric integral Gram matrix with even diagonal. The actual complex carrier consists of finitely supported charge families of oscillator polynomials.

**Definition 1.1 (Linear projection onto the fixed carrier).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Projection.plusProjection`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Projection.plusProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex-linear map from the actual carrier to the fixed carrier sends a state v to (v + theta(v)) / 2, the existing plusPart of the sign involution theta. Applying theta twice gives v, so the average is fixed.

**Theorem 1.2 (Evaluation on a fixed state).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Projection.plusProjection_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Projection.plusProjection_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projecting the underlying state of any element of the fixed carrier returns that element of the fixed carrier.

**Theorem 1.3 (Evaluation on an anti-invariant state).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Projection.plusProjection_odd`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Projection.plusProjection_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If theta(v) = -v, then the projection of v is zero in the fixed carrier.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Projection.plusProjection`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Projection.plusProjection_fixed`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Projection.plusProjection_odd`
- Dependency: [D5/S3/VertexAlgebra/LatticeInvolution](../../LatticeInvolution.md)
