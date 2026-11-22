# The Leech frame of 48 Virasoro states

## Abstract

Forty-eight explicit states whose central-charge-one-half Virasoro modes commute on the Leech orbifold.

Use both signs in each of the 24 directions of the actual norm-four frame. The states are distinct and their sum is the conformal state of the orbifold. The norm-four state formula retains the Dong-Mason-Zhu attribution recorded by Shimakura, arXiv:1202.6107, equation (1.3).

**Definition 1.1 (The signed axes).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.axis`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.axis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Embed the signed norm-four state from the fixed lattice sector with zero twisted component.

**Theorem 1.2 (Inverse Gram matrix).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.actualInverse_entry`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.actualInverse_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each inverse Gram entry is one quarter of the corresponding sum of charge outer products. The current-space basis has squared norm four, which determines its coordinate functionals.

**Theorem 1.3 (Sum of the axes).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.conformal_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.conformal_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The charged terms cancel within each signed pair. The inverse Gram identity identifies the remaining quadratic sum with the Sugawara stress state in the orbifold.

**Theorem 1.4 (Sum of the conformal modes).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.conformal_mode_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.conformal_mode_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Linearity of the original orbifold state-field map gives the mode sum on the whole carrier.

**Theorem 1.5 (Virasoro action of each axis).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.axis_virasoro`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.axis_virasoro` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each axis satisfies the integer-mode Virasoro relation at central charge one half on the fixed and odd twisted sectors.

**Theorem 1.6 (Mixed products in the lattice).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.lattice_mixed_products`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.lattice_mixed_products` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct indices in the same direction, the signs are opposite. For distinct directions, the charges are orthogonal. In either case every nonnegative product vanishes.

**Theorem 1.7 (Distinct axis states).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.axis_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.axis_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The third product of an axis with itself is a nonzero multiple of the vacuum. Together with mixed-product vanishing this proves injectivity.

**Theorem 1.8 (Mixed products in the orbifold).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.orbifold_mixed_products`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.orbifold_mixed_products` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed-source coefficient of the original orbifold field carries the lattice vanishing to the embedded axis states.

**Theorem 1.9 (Commuting modes of distinct axes).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.axis_modes_commute`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.axis_modes_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lattice and odd twisted commutator formulas express their commutators through the nonnegative mixed products. Every summand vanishes.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.actualInverse_entry`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.axis`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.axis_injective`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.axis_modes_commute`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.axis_virasoro`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.conformal_mode_sum`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.conformal_sum`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.lattice_mixed_products`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.orbifold_mixed_products`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame](ActualLeechNormFourFrame.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourVirasoroVector](../NormFourVirasoroVector.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing](../../TwistedGround/Orbifold/FixedSourceIsing.md)
