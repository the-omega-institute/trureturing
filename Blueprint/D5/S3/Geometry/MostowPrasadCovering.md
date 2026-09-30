# Isometric orbit coverings

## Abstract

Isometric representations connect to standard orbit quotients and covering maps.

The representation action identifies the project's orbit quotient with Mathlib's standard orbit quotient. Under explicit freeness and proper discontinuity assumptions, its projection is a topological covering map. No finite-volume lattice or hyperbolic geometry is constructed here.

**Definition 1.1 (Action associated with an isometric representation).**

Lean statement: `D5/S3/Geometry/MostowPrasadCovering.representationMulAction`

*Formalization.* `D5/S3/Geometry/MostowPrasadCovering.representationMulAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The group acts by applying its represented isometries.

**Definition 1.2 (Standard orbit quotient).**

Lean statement: `D5/S3/Geometry/MostowPrasadCovering.StandardOrbitQuotient`

*Formalization.* `D5/S3/Geometry/MostowPrasadCovering.StandardOrbitQuotient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib's orbit quotient for the representation action.

**Definition 1.3 (Free representation).**

Lean statement: `D5/S3/Geometry/MostowPrasadCovering.FreeRepresentation`

*Formalization.* `D5/S3/Geometry/MostowPrasadCovering.FreeRepresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only the identity group element fixes a point.

**Definition 1.4 (Properly discontinuous representation).**

Lean statement: `D5/S3/Geometry/MostowPrasadCovering.ProperlyDiscontinuousRepresentation`

*Formalization.* `D5/S3/Geometry/MostowPrasadCovering.ProperlyDiscontinuousRepresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only finitely many group elements move one compact set to meet another.

**Theorem 1.5 (Homeomorphism with the standard orbit quotient).**

Lean statement: `D5/S3/Geometry/MostowPrasadCovering.standardOrbitHomeomorph`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MostowPrasadCovering.standardOrbitHomeomorph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two orbit conventions give canonically homeomorphic quotient spaces.

**Theorem 1.6 (Covering projection for a free proper action).**

Lean statement: `D5/S3/Geometry/MostowPrasadCovering.orbitQuotientMk_isCoveringMap`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MostowPrasadCovering.orbitQuotientMk_isCoveringMap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient projection is a covering map when the representation is free and properly discontinuous on a locally compact Hausdorff space.

## References

- Truth anchor: `D5/S3/Geometry/MostowPrasadCovering.FreeRepresentation`
- Truth anchor: `D5/S3/Geometry/MostowPrasadCovering.ProperlyDiscontinuousRepresentation`
- Truth anchor: `D5/S3/Geometry/MostowPrasadCovering.StandardOrbitQuotient`
- Truth anchor: `D5/S3/Geometry/MostowPrasadCovering.orbitQuotientMk_isCoveringMap`
- Truth anchor: `D5/S3/Geometry/MostowPrasadCovering.representationMulAction`
- Truth anchor: `D5/S3/Geometry/MostowPrasadCovering.standardOrbitHomeomorph`
- Dependency: [D5/S3/Geometry/MostowPrasadDescent](MostowPrasadDescent.md)
