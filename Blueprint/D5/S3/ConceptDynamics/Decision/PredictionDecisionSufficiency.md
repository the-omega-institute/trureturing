# Prediction Sufficiency Implies Decision Sufficiency

## Abstract

A sufficient predictive readout determines expected losses and optimal actions.

**Theorem 1.1 (Prediction sufficiency implies decision sufficiency).**

$$\begin{gathered}\forall X, C, Y, A: \operatorname{Type},\\{}K: X \to \operatorname{PMF}(Y), CReadout: X \to C,\\{}\ell: A \to Y \to \mathbb{R},\\{}\operatorname{MeasurableSpace}(Y) \land \operatorname{MeasurableSingletonClass}(Y) \land\\{}(\forall x: X, a: A, \operatorname{Integrable}(\ell\left(a\right), \operatorname{toMeasure}(K\left(x\right)))),\\{}\forall x: X, a: A, \operatorname{expectedLoss}(K, \ell)\left(x, a\right) := \int_{Y} \ell\left(a, y\right)\,dK\left(x\right),\\{}\forall x: X, \operatorname{optimalActions}(K, \ell)\left(x\right) := \operatorname{argmin}_{a\in A} \operatorname{expectedLoss}(K, \ell)\left(x, a\right),\\{}\operatorname{Refines}(K, CReadout) \Rightarrow\\{}\operatorname{Refines}(\operatorname{expectedLoss}(K, \ell), CReadout) \land \operatorname{Refines}(\operatorname{optimalActions}(K, \ell), CReadout).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/PredictionDecisionSufficiency.prediction_sufficiency_implies_decision_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The outcome carrier has discrete measurable points, and every displayed action loss is integrable under every predicted law.

Expected loss is the integral of the supplied loss against the same PMF readout appearing in the refinement premise. The optimal-action readout is the full argmin set of that expected-loss profile.

Composing both constructions with the prediction factor map proves the two refinement clauses simultaneously.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Decision/PredictionDecisionSufficiency.prediction_sufficiency_implies_decision_sufficiency`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
