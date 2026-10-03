# Hyperbolic dilations

## Abstract

Positive dilations of hyperbolic upper half-space.

Scaling both horizontal coordinates and height by a positive real preserves the normalized upper half-space distance. The inverse scale gives an isometric equivalence. This does not establish completeness, curvature, cusp volume, or rigidity.

**Definition 1.1 (Positive dilation).**

Lean statement: `D5/S3/Geometry/HyperbolicDilation.positiveDilation`

*Formalization.* `D5/S3/Geometry/HyperbolicDilation.positiveDilation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Scale every coordinate by the same positive real.

**Theorem 1.2 (Distance preservation).**

Lean statement: `D5/S3/Geometry/HyperbolicDilation.hyperbolicDist_positiveDilation`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/HyperbolicDilation.hyperbolicDist_positiveDilation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Euclidean distance and height normalization scale equally.

**Definition 1.3 (Isometric equivalence).**

Lean statement: `D5/S3/Geometry/HyperbolicDilation.dilation`

*Formalization.* `D5/S3/Geometry/HyperbolicDilation.dilation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positive dilation has the inverse dilation by the reciprocal.

## References

- Truth anchor: `D5/S3/Geometry/HyperbolicDilation.dilation`
- Truth anchor: `D5/S3/Geometry/HyperbolicDilation.hyperbolicDist_positiveDilation`
- Truth anchor: `D5/S3/Geometry/HyperbolicDilation.positiveDilation`
- Dependency: [D5/S3/Geometry/HyperbolicUpperHalfSpace](HyperbolicUpperHalfSpace.md)
