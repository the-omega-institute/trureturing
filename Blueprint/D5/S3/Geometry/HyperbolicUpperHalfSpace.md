# Hyperbolic upper half-space metric

## Abstract

The Ptolemy proof of the upper half-space metric and horizontal isometries.

Positive-height coordinates carry the standard upper half-space distance. A reflected-point Ptolemy estimate proves its metric laws in any real inner product horizontal space. Horizontal translations give a faithful isometric action. Curvature, completeness, finite volume, cusps, and Mostow--Prasad rigidity are not established by these declarations.

**Definition 1.1 (Positive-height coordinates).**

Lean statement: `D5/S3/Geometry/HyperbolicUpperHalfSpace.UpperHalfSpace`

*Formalization.* `D5/S3/Geometry/HyperbolicUpperHalfSpace.UpperHalfSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Points of a Euclidean product with positive height.

**Definition 1.2 (Upper half-space distance formula).**

Lean statement: `D5/S3/Geometry/HyperbolicUpperHalfSpace.hyperbolicDist`

*Formalization.* `D5/S3/Geometry/HyperbolicUpperHalfSpace.hyperbolicDist` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Twice the inverse hyperbolic sine of the normalized Euclidean separation.

**Theorem 1.3 (Triangle inequality).**

Lean statement: `D5/S3/Geometry/HyperbolicUpperHalfSpace.hyperbolicDist_triangle`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/HyperbolicUpperHalfSpace.hyperbolicDist_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reflection and Euclidean Ptolemy yield the hyperbolic triangle inequality.

**Definition 1.4 (Metric-space instance).**

Lean statement: `D5/S3/Geometry/HyperbolicUpperHalfSpace.hyperbolicMetricSpace`

*Formalization.* `D5/S3/Geometry/HyperbolicUpperHalfSpace.hyperbolicMetricSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The distance formula equips the distinct upper half-space type with a metric.

**Definition 1.5 (Horizontal isometric representation).**

Lean statement: `D5/S3/Geometry/HyperbolicUpperHalfSpace.horizontalRepresentation`

*Formalization.* `D5/S3/Geometry/HyperbolicUpperHalfSpace.horizontalRepresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Horizontal addition acts through hyperbolic isometries.

**Theorem 1.6 (Fixed point criterion).**

Lean statement: `D5/S3/Geometry/HyperbolicUpperHalfSpace.horizontalTranslation_fixed_iff_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/HyperbolicUpperHalfSpace.horizontalTranslation_fixed_iff_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A horizontal translation fixing one point has zero translation vector.

## References

- Truth anchor: `D5/S3/Geometry/HyperbolicUpperHalfSpace.UpperHalfSpace`
- Truth anchor: `D5/S3/Geometry/HyperbolicUpperHalfSpace.horizontalRepresentation`
- Truth anchor: `D5/S3/Geometry/HyperbolicUpperHalfSpace.horizontalTranslation_fixed_iff_zero`
- Truth anchor: `D5/S3/Geometry/HyperbolicUpperHalfSpace.hyperbolicDist`
- Truth anchor: `D5/S3/Geometry/HyperbolicUpperHalfSpace.hyperbolicDist_triangle`
- Truth anchor: `D5/S3/Geometry/HyperbolicUpperHalfSpace.hyperbolicMetricSpace`
