# Hyperbolic completeness

## Abstract

Completeness of the hyperbolic upper-half-space metric.

When the horizontal real inner product space is complete, its hyperbolic upper half-space is complete. A hyperbolic Cauchy sequence has Cauchy Euclidean coordinates and Cauchy logarithmic heights; the limiting height remains positive. This establishes completeness of the model. Manifold curvature, quotient completeness, finite-volume cusps, and Mostow--Prasad rigidity remain separate obligations.

**Theorem 1.1 (Logarithmic height bound).**

Lean statement: `D5/S3/Geometry/HyperbolicCompleteness.dist_log_height_le`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/HyperbolicCompleteness.dist_log_height_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The difference of log-heights is bounded by the normalized distance.

**Definition 1.2 (Complete-space instance).**

Lean statement: `D5/S3/Geometry/HyperbolicCompleteness.hyperbolicCompleteSpace`

*Formalization.* `D5/S3/Geometry/HyperbolicCompleteness.hyperbolicCompleteSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinate completeness and the positive exponential limit of height yield hyperbolic convergence.

## References

- Truth anchor: `D5/S3/Geometry/HyperbolicCompleteness.dist_log_height_le`
- Truth anchor: `D5/S3/Geometry/HyperbolicCompleteness.hyperbolicCompleteSpace`
- Dependency: [D5/S3/Geometry/HyperbolicUpperHalfSpace](HyperbolicUpperHalfSpace.md)
