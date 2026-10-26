# Hausdorff Dimension of an Involution Orbit Space

## Abstract

The metric quotient by an isometric involution preserves the Hausdorff dimension of every subset of a second-countable metric space, including fixed points.

**Definition 1.1 (The two-element isometric action).**

Lean statement: `D5/S3/Geometry/InvolutionOrbitDimension.representation`

*Formalization.* `D5/S3/Geometry/InvolutionOrbitDimension.representation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An involutive isometry generates the action of the two-element group. The identity acts trivially and the other element acts by the supplied isometry.

**Definition 1.2 (The actual finite orbit space).**

Lean statement: `D5/S3/Geometry/InvolutionOrbitDimension.Orbit`

*Formalization.* `D5/S3/Geometry/InvolutionOrbitDimension.Orbit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the quotient by that action. The metric is the existing finite-action orbit metric: the distance between classes represented by x and y is the minimum of the distance from x to y and from x to the involute of y. The metric uses the quotient topology; fixed points are retained.

**Definition 1.3 (The orbit projection).**

Lean statement: `D5/S3/Geometry/InvolutionOrbitDimension.project`

*Formalization.* `D5/S3/Geometry/InvolutionOrbitDimension.project` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The projection sends a point to its actual orbit class. It is one-Lipschitz.

**Theorem 1.4 (Hausdorff dimension is preserved).**

$$\forall X\in\operatorname{Type}\left(\right),[\operatorname{MetricSpace}\left(X\right)] [\operatorname{SecondCountableTopology}\left(X\right)],\\\forall c\in\operatorname{IsometryEquiv}\left(X, X\right),h\in\operatorname{Involutive}\left(c\right),s\in\operatorname{Set}\left(X\right),\operatorname{dimH}\left(\operatorname{image}\left(\operatorname{project}\left(c, h\right), s\right)\right)=\operatorname{dimH}\left(s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/InvolutionOrbitDimension.dimH_project` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No freeness, convexity, finite dimension, or invariance of the subset is assumed. The dimension is Hausdorff dimension in the stated metrics.

Around a point that is moved by the involution, any ball with radius at most one quarter of its displacement maps isometrically to the quotient. Second countability supplies a countable cover by such balls. On the fixed locus the projection is itself an isometry. Countable stability of Hausdorff dimension gives the lower bound; the Lipschitz projection gives the upper bound.

## References

- Truth anchor: `D5/S3/Geometry/InvolutionOrbitDimension.Orbit`
- Truth anchor: `D5/S3/Geometry/InvolutionOrbitDimension.dimH_project`
- Truth anchor: `D5/S3/Geometry/InvolutionOrbitDimension.project`
- Truth anchor: `D5/S3/Geometry/InvolutionOrbitDimension.representation`
- Dependency: [D5/S3/Geometry/IsometricOrbitMetric](IsometricOrbitMetric.md)
