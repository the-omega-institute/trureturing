# The actual core and occupied lines recover every value

## Abstract

The actual core and occupied lines recover every value.

**Theorem 1.1 (Complete function recovery).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraFiberInverse.same_core_same_active_equal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraFiberInverse.same_core_same_active_equal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix two normalized unit-edge arrays on the same rectangle, each in the exact residual class with a minima and b maxima. Suppose both legally reduce to the same individual core function, with no adjacent frozen lines on either axis. If their occupied columns and occupied rows agree at every physical coordinate, the complete height functions agree. Delete an adjacent frozen pair at the same position in both arrays. Exact extremum transport preserves the agreement of occupied coordinates. Normalization and actual core uniqueness ensure that both contracted arrays still reduce to the given core. Induction identifies these smaller complete functions. The frozen slope surviving at the seam identifies the signed step of the deleted line, and the signed restore inverse recovers every cell. If no adjacent pair remains on either axis, both arrays are already the same actual reduced core.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraFiberInverse.same_core_same_active_equal`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCanonicalColumns](MiuraCanonicalColumns.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCanonicalJoint](MiuraCanonicalJoint.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreJoint](MiuraCoreJoint.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreNormal](MiuraCoreNormal.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreTranspose](MiuraCoreTranspose.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraFiberCore](MiuraFiberCore.md)
