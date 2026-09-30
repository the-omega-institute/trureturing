# Hyperbolic inversion

## Abstract

Boundary-centered inversion of hyperbolic upper half-space.

Euclidean inversion about the boundary origin preserves positive height and the normalized upper-half-space distance in any real inner product horizontal space. It is an involutive isometric equivalence. This does not construct the ideal boundary, classify the full isometry group, or prove Mostow--Prasad rigidity.

**Definition 1.1 (Inverted upper-half-space point).**

Lean statement: `D5/S3/Geometry/HyperbolicInversion.invertedPoint`

*Formalization.* `D5/S3/Geometry/HyperbolicInversion.invertedPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive-height restriction of unit-radius Euclidean inversion.

**Theorem 1.2 (Distance preservation).**

Lean statement: `D5/S3/Geometry/HyperbolicInversion.hyperbolicDist_invertedPoint`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/HyperbolicInversion.hyperbolicDist_invertedPoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Euclidean separation and the height geometric mean acquire the same reciprocal factor.

**Definition 1.3 (Involutive isometric equivalence).**

Lean statement: `D5/S3/Geometry/HyperbolicInversion.inversion`

*Formalization.* `D5/S3/Geometry/HyperbolicInversion.inversion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Euclidean inversion squared is the identity on positive-height points.

## References

- Truth anchor: `D5/S3/Geometry/HyperbolicInversion.hyperbolicDist_invertedPoint`
- Truth anchor: `D5/S3/Geometry/HyperbolicInversion.inversion`
- Truth anchor: `D5/S3/Geometry/HyperbolicInversion.invertedPoint`
- Dependency: [D5/S3/Geometry/HyperbolicDilation](HyperbolicDilation.md)
