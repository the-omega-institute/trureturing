# Hyperbolic topology

## Abstract

Topology and compact closed balls of hyperbolic upper half-space.

The normalized hyperbolic metric induces the usual topology on the positive-height upper half-space over any real inner product space. When the horizontal metric space is proper, all hyperbolic closed balls are compact. The proof controls height above and below and bounds horizontal separation on each ball. This concerns the model space; manifold curvature, quotient completeness, finite-volume cusps, and Mostow--Prasad rigidity remain separate obligations.

**Definition 1.1 (Coordinate homeomorphism).**

Lean statement: `D5/S3/Geometry/HyperbolicTopology.coordinatesHomeomorph`

*Formalization.* `D5/S3/Geometry/HyperbolicTopology.coordinatesHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate bijection is continuous in both directions, using the logarithmic height estimate and the exact distance formula.

**Definition 1.2 (Proper-space instance).**

Lean statement: `D5/S3/Geometry/HyperbolicTopology.hyperbolicProperSpace`

*Formalization.* `D5/S3/Geometry/HyperbolicTopology.hyperbolicProperSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A hyperbolic closed ball is a closed subset of the continuous image of a compact horizontal ball times a positive height interval.

## References

- Truth anchor: `D5/S3/Geometry/HyperbolicTopology.coordinatesHomeomorph`
- Truth anchor: `D5/S3/Geometry/HyperbolicTopology.hyperbolicProperSpace`
- Dependency: [D5/S3/Geometry/HyperbolicCompleteness](HyperbolicCompleteness.md)
