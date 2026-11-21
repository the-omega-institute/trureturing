# The signed four-column branch

## Abstract

At four columns the two signed evaluations of a pair indicator separate edges and diagonals directly.

**Theorem 1.1 (The signed quadratic on pairs).**

Lean statement: `D5/S3/Geometry/KozakiKakeiFour.signed_four_evaluation`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiFour.signed_four_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The indicator of two distinct columns gives one on edges and minus two on diagonals.

**Theorem 1.2 (Four-column necessity).**

Lean statement: `D5/S3/Geometry/KozakiKakeiFour.dihedral_of_scalar_four`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiFour.dihedral_of_scalar_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Among the images of the two edges incident with a fixed vertex, at least one is an edge. The scalar must be one, so every edge maps to an edge.

**Theorem 1.3 (Necessity on the whole size range).**

Lean statement: `D5/S3/Geometry/KozakiKakeiFour.dihedral_of_preservesLevel`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiFour.dihedral_of_preservesLevel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply scalar rigidity to the admissible constant matrices. Then use signed pair evaluations for m equal to two and recovery by support counts for every m at least four.

## References

- Truth anchor: `D5/S3/Geometry/KozakiKakeiFour.dihedral_of_preservesLevel`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiFour.dihedral_of_scalar_four`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiFour.signed_four_evaluation`
- Dependency: [D5/S3/Geometry/KozakiKakeiSupport](KozakiKakeiSupport.md)
