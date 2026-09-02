# Curvature-Slack Phase Bridge

## Abstract

Normalized curvature is the compact coordinate; degree-one slack is its complementary square and reciprocal inputs reverse its phase.

**Theorem 1.1 (Curvature, slack, and reciprocal phase).**

$$\begin{gathered}\forall a, x: \mathbb{R},\\{}(0 < a) \land (0 \leq x) \Rightarrow\\{}\operatorname{let} z = \frac{x - a}{x + a}; \operatorname{let} \kappa = \frac{2 \cdot (x - a)}{(x + a)^{2}}; \operatorname{let} s = 1 - T_{1}(z)^{2}; (\frac{(x + a) \cdot \kappa}{2}^{2} + s = 1) \land\\{}(\frac{(x + a) \cdot \kappa}{2} = z) \land\\{}((0 < x < a) \Rightarrow\\{}\operatorname{let} y = \frac{a^{2}}{x}; (\frac{y - a}{y + a} = -z) \land\\{}(1 - T_{1}(\frac{y - a}{y + a})^{2} = s) \land\\{}(z < 0) \land\\{}(0 < \frac{y - a}{y + a})).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CayleyLaguerre/CurvatureSlackPhaseBridge.curvature_slack_phase_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate, curvature scalar, and degree-one Chebyshev slack are constructed from a positive scale and nonnegative input.

Normalization recovers the coordinate and gives a unit sum with slack. For a strictly positive input below the scale, the reciprocal coordinate is its negative, so slack is unchanged while the two coordinate signs are opposite.

## References

- Truth anchor: `D5/S3/Weil/CayleyLaguerre/CurvatureSlackPhaseBridge.curvature_slack_phase_bridge`
- Dependency: [D5/S3/Analytic/Adelic/OffLineCurvatureDipole](../../Analytic/Adelic/OffLineCurvatureDipole.md)
- Dependency: [D5/S3/Weil/CayleyLaguerre/ChebyshevSlackPositivity](ChebyshevSlackPositivity.md)
