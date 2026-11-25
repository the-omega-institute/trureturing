# Pairwise stability of length-weighted curvature descent

## Abstract

Positive trajectories of a multiplicatively weighted monotone field have quantitative pairwise stability without assuming local Lipschitz regularity of the field.

**Theorem 1.1 (A square-root distance bound for the weighted flow).**

Lean statement: `D5/S3/Geometry/Hyperideal/WeightedCurvatureFlowStability.weighted_stability`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/WeightedCurvatureFlowStability.weighted_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the chart z=2 sqrt(length) on each positive coordinate. The coordinate-square identity splits the two-point derivative into ordinary length-space monotonicity and a diagonal term involving the sum of the two residuals.

A one-sided lower bound of minus C on those residuals gives a squared chart distance growth factor exp(C times elapsed time). The chart distance separates positive lengths, so identical initial lengths give uniqueness among existing trajectories.

This is a differential comparison for existing trajectories. It neither constructs solutions nor formalizes the extension of hyperideal covolume, the three interval Hessian certificates, or general degree-seven realization.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/WeightedCurvatureFlowStability.weighted_stability`
