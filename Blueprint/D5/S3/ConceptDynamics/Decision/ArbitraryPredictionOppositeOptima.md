# Arbitrary Prediction, Opposite Optimal Actions

## Abstract

Every PMF prediction admits opposite unique optima under two constant loss models.

**Theorem 1.1 (Any fixed predictive law is compatible with opposite unique optima).**

$$\begin{gathered}\forall X, Y: \operatorname{Type},\\{}\operatorname{MeasurableSpace}\left(Y\right) \land \operatorname{MeasurableSingletonClass}\left(Y\right),\\{}K: X \to \operatorname{PMF}\left(Y\right),\\{}\operatorname{let} ellL: Bool \to Y \to \mathbb{R}, \forall a: Bool, y: Y, ellL\left(a, y\right) := \operatorname{if}\left(a, 1, 0\right); \\{}\operatorname{let} ellR: Bool \to Y \to \mathbb{R}, \forall a: Bool, y: Y, ellR\left(a, y\right) := \operatorname{if}\left(a, 0, 1\right); \\{}\operatorname{let} Risk: (Bool \to Y \to \mathbb{R}) \to X \to Bool \to \mathbb{R}, \forall ell: Bool \to Y \to \mathbb{R}, x: X, a: Bool, Risk\left(ell, x, a\right) := \operatorname{integral}\left(\operatorname{toMeasure}\left(K\left(x\right)\right), ell\left(a\right)\right); \\{}\operatorname{let} Opt: (Bool \to Y \to \mathbb{R}) \to X \to \operatorname{Set}\left(Bool\right), \forall ell: Bool \to Y \to \mathbb{R}, x: X, Opt\left(ell, x\right) := \left\{a: Bool \mid \forall b \in Bool,\; Risk\left(ell, x, a\right) \le Risk\left(ell, x, b\right)\right\}; \\{}(\forall x \in X,\; Opt\left(ellL, x\right) = \left\{false\right\}) \land (\forall x \in X,\; Opt\left(ellR, x\right) = \left\{true\right\}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/ArbitraryPredictionOppositeOptima.arbitrary_prediction_opposite_unique_optima` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same arbitrary PMF-valued prediction is used for both losses. The false action has constant losses zero and one respectively, while the true action has constant losses one and zero.

Expected loss is constructed by integrating each action loss against the supplied predictive PMF. The displayed optimal-action sets are the full pointwise argmin sets, not separately chosen selectors.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Decision/ArbitraryPredictionOppositeOptima.arbitrary_prediction_opposite_unique_optima`
- Dependency: [D5/S3/ConceptDynamics/Decision/PredictionLawDecisionSufficiency](PredictionLawDecisionSufficiency.md)
