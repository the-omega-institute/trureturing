# Invertible matrix operations and the level equation

## Abstract

Row operations and column scalings multiply both determinant products by the same nonzero factor.

**Definition 1.1 (Row operations).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.Square`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatrixEquiv.Square` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The square matrix type has two rows and two columns over the rational function field.

**Definition 1.2 (Left and right multiplication).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.scaled`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatrixEquiv.scaled` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the square matrix on the left and the diagonal of the column factors on the right.

**Theorem 1.3 (Entries after scaling).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.scaled_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiMatrixEquiv.scaled_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the two-term row combination and multiply by the column factor.

**Theorem 1.4 (Determinant transformation).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.minor_scaled`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiMatrixEquiv.minor_scaled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each minor acquires the determinant of the left matrix and the two column factors.

**Theorem 1.5 (Admissibility after invertible scaling).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.scaled_admissible`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiMatrixEquiv.scaled_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All the factors in the scaled minor remain nonzero.

**Theorem 1.6 (Invertible matrices have nonzero determinant).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.unit_det_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiMatrixEquiv.unit_det_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An invertible square matrix has unit determinant in the coefficient field.

**Theorem 1.7 (Invariance of the written level).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.level_scaled_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiMatrixEquiv.level_scaled_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each matching uses every column once. Both products acquire the determinant to the m-th power times the product of all column factors, which can be canceled.

**Theorem 1.8 (Composition of row and column operations).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.scaled_comp`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiMatrixEquiv.scaled_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Left factors multiply in application order and right scalars multiply pointwise.

**Theorem 1.9 (Symmetry of matrix equivalence).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.matEquivalent_symm`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiMatrixEquiv.matEquivalent_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Invert the left matrix and each column factor.

**Theorem 1.10 (Transitivity of matrix equivalence).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.matEquivalent_trans`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiMatrixEquiv.matEquivalent_trans` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compose the left operations and multiply the diagonal factors pointwise.

**Theorem 1.11 (Transport of matrix equivalence).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.reorder_equiv`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiMatrixEquiv.reorder_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same left matrix and the correspondingly permuted diagonal factors implement equivalence after column reordering.

**Theorem 1.12 (Transport of admissibility).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.reorder_admissible`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiMatrixEquiv.reorder_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A permutation takes distinct columns to distinct columns.

**Theorem 1.13 (Level invariance under matrix equivalence).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.level_equiv`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiMatrixEquiv.level_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unit witnesses make the common factor nonzero, so matrix-equivalent inputs satisfy the same level equation.

## References

- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.Square`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.level_equiv`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.level_scaled_iff`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.matEquivalent_symm`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.matEquivalent_trans`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.minor_scaled`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.reorder_admissible`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.reorder_equiv`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.scaled`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.scaled_admissible`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.scaled_apply`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.scaled_comp`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatrixEquiv.unit_det_ne_zero`
- Dependency: [D5/S3/Geometry/KozakiKakeiPreservation](KozakiKakeiPreservation.md)
