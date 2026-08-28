# Conditional Expectation Zero-Risk Criterion

## Abstract

Zero conditional squared-error risk exactly characterizes almost-everywhere measurability for the observation-generated sigma-algebra.

**Theorem 1.1 (Zero prediction risk characterizes observable targets).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}[\operatorname{MeasurableSpace}\left(X\right)], [\operatorname{MeasurableSpace}\left(O\right)],\\{}mu: \operatorname{Measure}\left(X\right), [\operatorname{IsProbabilityMeasure}\left(mu\right)],\\{}q: X \to O, \operatorname{Measurable}\left(q\right),\\{}T: X \to \mathbb{R}, \operatorname{MemLp}\left(T, 2, mu\right)\\{}\Rightarrow (\operatorname{Integral}\left({T - \operatorname{condExp}\left(T, \operatorname{comap}\left(q\right), mu\right)}^{{2}}, mu\right) = 0) \iff\\{}\operatorname{AEStronglyMeasurable}\left(T, \operatorname{comap}\left(q\right), mu\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Prediction/ConditionalExpectationZeroRiskCriterion.zero_prediction_risk_iff_ae_observation_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The measurable observation map constructs its visible sigma-algebra by measurable-space comap. The displayed conditional expectation is Mathlib's canonical predictor on that sigma-algebra.

Square integrability makes the pointwise squared residual integrable. Its nonnegative integral is zero precisely when the residual vanishes almost everywhere. The conditional expectation is measurable on the generated sigma-algebra, and its measurable fixed-point theorem gives the converse.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Prediction/ConditionalExpectationZeroRiskCriterion.zero_prediction_risk_iff_ae_observation_measurable`
- Dependency: [D5/S3/ConceptDynamics/Prediction/ConditionalExpectationOptimality](ConditionalExpectationOptimality.md)
