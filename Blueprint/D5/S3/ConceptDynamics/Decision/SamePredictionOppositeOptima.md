# Same Prediction, Opposite Optimal Actions

## Abstract

One PMF prediction admits opposite unique optima under two loss models.

**Theorem 1.1 (A predictive law does not determine value).**

$$\exists K: Bool \to \operatorname{PMF}\left(Unit\right), ell_{0}, ell_{1}: Bool \to (Unit \to \mathbb{R}),\\{}\operatorname{let} Risk: (Bool \to (Unit \to \mathbb{R})) \to Bool \to Bool \to \mathbb{R}, \forall ell: Bool \to (Unit \to \mathbb{R}), x: Bool, a: Bool, Risk\left(ell, x, a\right) := \operatorname{integral}\left(\operatorname{toMeasure}\left(K\left(x\right)\right), ell\left(a\right)\right); \\{}\operatorname{let} Opt: (Bool \to (Unit \to \mathbb{R})) \to Bool \to \operatorname{Set}\left(Bool\right), \forall ell: Bool \to (Unit \to \mathbb{R}), x: Bool, Opt\left(ell, x\right) := \left\{a: Bool \mid \forall b \in Bool,\; Risk\left(ell, x, a\right) \le Risk\left(ell, x, b\right)\right\}; \\{}(\forall x \in Bool,\; Opt\left(ell_{0}, x\right) = \left\{false\right\}) \land (\forall x \in Bool,\; Opt\left(ell_{1}, x\right) = \left\{true\right\}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/SamePredictionOppositeOptima.same_prediction_opposite_unique_optima` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A single Boolean-state prediction interface is constructed as a PMF on Unit. Two Boolean-action loss models are quantified together with that same interface, and both expected-loss profiles use its PMF through the canonical toMeasure integral.

The complete optimizer set is the singleton false action under the first loss and the singleton true action under the second loss, for every state. Thus the predictive PMF alone does not determine which action has value.

The imported decision-family owner supplies the expectation and full optimizer-set shapes. Repository and pinned-Mathlib searches found no theorem packaging this opposite-optimum countermodel.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Decision/SamePredictionOppositeOptima.same_prediction_opposite_unique_optima`
- Dependency: [D5/S3/ConceptDynamics/Decision/PredictionDecisionSufficiency](PredictionDecisionSufficiency.md)
