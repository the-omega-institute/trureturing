# Affine general position on a sphere

## Abstract

Finite affine-general-position configurations on positive-radius round spheres.

These are classical general-position constructions. The proper-affine-span dimension bound and the affine-independence insertion criterion are reused from Mathlib; selection on the sphere uses the rational-circle finite-avoidance construction. No literature priority or graph-level realization result is asserted.

**Theorem 1.1 (Joint avoidance of proper affine subspaces).**

Lean statement: `D5/S3/Geometry/SphereGeneralPosition.exists_on_sphere_avoiding_affine_subspaces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/SphereGeneralPosition.exists_on_sphere_avoiding_affine_subspaces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In any finite-dimensional real inner product space of dimension at least two, every ambient-open patch meeting a positive-radius sphere has a point outside each member of any specified finite family of proper affine subspaces. Empty affine subspaces need no exclusion. For a nonempty proper affine subspace, its direction is proper and has a nonzero perpendicular normal. A fixed point determines its affine offset, so the sphere-section avoidance theorem applies.

**Theorem 1.2 (Every finite cardinality in affine general position).**

Lean statement: `D5/S3/Geometry/SphereGeneralPosition.exists_sphere_general_position`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/SphereGeneralPosition.exists_sphere_general_position` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and every positive real r there is a finite set s of cardinality n on the norm-r sphere such that every subset t of s with at most dim(E)+1 elements is affinely independent. The ambient finite-dimensional real inner product space E has dimension at least two. At each finite induction step the new point avoids the affine span of every old subset of size at most dim(E). These are proper affine subspaces by the cardinality bound. Avoiding singleton spans prevents collisions; the insertion criterion establishes independence for every newly formed subset. The case n=0 is included. For a three-dimensional carrier this gives any finite number of points on a two-sphere with every four independent; a four-dimensional carrier gives points on a three-sphere with every five independent.

## References

- Truth anchor: `D5/S3/Geometry/SphereGeneralPosition.exists_on_sphere_avoiding_affine_subspaces`
- Truth anchor: `D5/S3/Geometry/SphereGeneralPosition.exists_sphere_general_position`
- Dependency: [D5/S3/Geometry/SphereSectionAvoidance](SphereSectionAvoidance.md)
