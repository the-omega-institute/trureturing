# Uniqueness of the actual joint reduced core

## Abstract

Uniqueness of the actual joint reduced core.

The one-step diamond uses equality for overlapping choices in one frozen run, commutation with shifted indices for separated choices on one axis, and exact row-column commutation for orthogonal choices. The pinned Church-Rosser theorem joins arbitrary finite sequences. A rectangle with no adjacent frozen pair admits no further step, so both endpoints equal the common descendant.

**Theorem 1.1 (Every deletion choice gives the same actual reduced rectangle).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCanonicalJoint.joint_reduced_core_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCanonicalJoint.joint_reduced_core_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let h be any actual unit-edge integer height function. Suppose JointReduction h g and JointReduction h f are arbitrary legal sequences, and both g and f have no adjacent frozen pair along either physical axis. Then the dependent pairs consisting of the row dimension, the column dimension, and the complete integer function are equal. Thus both dimensions agree and the functions agree under the resulting dimension transport. No normalization or quotient is introduced; in particular this equality applies to the normalized residual arrays.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCanonicalJoint.joint_reduced_core_unique`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCanonicalColumns](MiuraCanonicalColumns.md)
