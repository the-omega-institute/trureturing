# The antipodal zero matching

## Abstract

Rank loss in a three-cube and capacity of a four-face

**Theorem 1.1 (Classify singular restrictions).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourFaceDefect.submatrix_has_nonzero_kernel_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourFaceDefect.submatrix_has_nonzero_kernel_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An orthogonal four-by-four block whose zeros form a matching can lose rank after restriction to selected columns and rows. A surplus of columns suffices. At equal sizes, the retained or omitted antipodal singleton characterizes the singular exceptions.

**Theorem 1.2 (Bound the exterior of a witnessed face).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourFaceDefect.exterior_card_le_three`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourFaceDefect.exterior_card_le_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restore the dominant coordinate as a two-point fibre. The rank witness specifies the double fibres and the empty opposite-parity fibres. Subcubicity and the antipodal matching give a capacity of at most three vertices outside the closed neighborhood.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourFaceDefect.exterior_card_le_three`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourFaceDefect.submatrix_has_nonzero_kernel_iff`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
