# Path-Connectedness of Golden Displacement Series Values

## Abstract

The attained golden displacement values form a path-connected set with no gaps above one.

The exact convergence region is convex, and the golden displacement sum is continuous on that region. The unattained greatest lower bound at one supplies an attained value and hence a point in the convergence region. The region and its continuous image are therefore path-connected.

**Theorem 1.1 (The attained value set is path-connected).**

$$\operatorname{IsPathConnected}(\left\{x : \mathbb{R} \mid \exists s, w \in \mathbb{R}, \operatorname{Summable}(\operatorname{dTerm}(s, w)) \land\\\sum_{n=0}^{\infty} \operatorname{dTerm}(s, w, n) = x\right\})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Connectivity/GoldenDisplacementSeriesValueConnectedness.golden_displacement_series_values_isPathConnected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The greatest-lower-bound and nonattainment declarations produce an attained value strictly between one and two. Its parameters give a point in the exact convergence region.

That region is convex and nonempty, hence path-connected. Continuity of the series sum on this exact domain makes its image path-connected, and the image is exactly the displayed two-parameter value set.

**Theorem 1.2 (Every intermediate value above one is attained).**

$$\forall x \in \left\{x : \mathbb{R} \mid \exists s, w \in \mathbb{R}, \operatorname{Summable}(\operatorname{dTerm}(s, w)) \land\\\sum_{n=0}^{\infty} \operatorname{dTerm}(s, w, n) = x\right\},\\\operatorname{Ioo}(1, x) \subseteq \left\{x : \mathbb{R} \mid \exists s, w \in \mathbb{R}, \operatorname{Summable}(\operatorname{dTerm}(s, w)) \land\\\sum_{n=0}^{\infty} \operatorname{dTerm}(s, w, n) = x\right\}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Connectivity/GoldenDisplacementSeriesValueConnectedness.Ioo_one_subset_golden_displacement_series_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given an attained value x and a real y strictly between one and x, the greatest-lower-bound theorem and nonattainment of one provide an attained value z strictly between one and y. Order-connectedness of the path-connected value set then places y between the attained endpoints z and x, so y is attained.

These theorems do not identify the value set with the open ray above one, assert that every real greater than one is attained, prove that the value set is unbounded above, or claim divergence to infinity at the boundary of the convergence region.

## References

- Truth anchor: `D5/S3/Analytic/Connectivity/GoldenDisplacementSeriesValueConnectedness.Ioo_one_subset_golden_displacement_series_values`
- Truth anchor: `D5/S3/Analytic/Connectivity/GoldenDisplacementSeriesValueConnectedness.golden_displacement_series_values_isPathConnected`
- Dependency: [D5/S3/Analytic/Boundary/GoldenDisplacementSeriesContinuity](../Boundary/GoldenDisplacementSeriesContinuity.md)
- Dependency: [D5/S3/Analytic/Extrema/GoldenDisplacementSeriesInfimum](../Extrema/GoldenDisplacementSeriesInfimum.md)
