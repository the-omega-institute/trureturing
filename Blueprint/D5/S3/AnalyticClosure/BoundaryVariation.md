# Boundary Variation

## Abstract

The rational variation law tends to one third at the integer boundary.

**Theorem 1.1 (The boundary variation tends to one third).**

$$\lim_{beta\to2} \frac{beta^{2}-beta-1}{beta^{2}-1} = \frac{1}{3}.$$

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/BoundaryVariation.boundary_variation_tendsto_one_third` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the rational variation law V(beta) = (beta^2 - beta - 1)/(beta^2 - 1), the denominator is nonzero at beta = 2. Continuity of powers, subtraction, and division therefore makes the limit equal to the value at that boundary, namely 1/3.

The Lean proof directly reuses Mathlib's ContinuousAt.div after checking the nonzero denominator, then normalizes the boundary value.

This closes only the boundary-continuity sentence in remark 27.781, clause 2. It does not derive the variation formula for the beta family, the d >= 3 values, or the separate degenerate d = 2 case.

## References

- Truth anchor: `D5/S3/AnalyticClosure/BoundaryVariation.boundary_variation_tendsto_one_third`
