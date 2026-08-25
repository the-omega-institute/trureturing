# Predictive-Law Sufficiency Implies Decision Sufficiency

## Abstract

A predictive-law factor determines expected losses and their minimizing actions.

**Theorem 1.1 (Predictive-law sufficiency implies decision sufficiency).**

$$\begin{gathered}\forall X, C, Y, A: \operatorname{Type},\\{}K: X \to \operatorname{PMF}(Y), CReadout: X \to C,\\{}\ell: A \to Y \to \mathbb{R},\\{}\operatorname{MeasurableSpace}(Y) \land \operatorname{MeasurableSingletonClass}(Y),\\{}\forall x: X, a: A, \operatorname{expectedLoss}(K, \ell)\left(x, a\right) := \int_{Y} \ell\left(a, y\right)\,dK\left(x\right),\\{}\forall x: X, \operatorname{optimalActions}(K, \ell)\left(x\right) := \operatorname{argmin}_{a\in A} \operatorname{expectedLoss}(K, \ell)\left(x, a\right),\\{}\operatorname{Refines}(K, CReadout) \Rightarrow\\{}\operatorname{Refines}(\operatorname{expectedLoss}(K, \ell), CReadout) \land \operatorname{Refines}(\operatorname{optimalActions}(K, \ell), CReadout).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/PredictionLawDecisionSufficiency.prediction_law_sufficiency_implies_decision_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expected loss is the total Lean integral of each action loss against the predicted PMF; no integrability premise is required to construct it.

The optimal-action readout is the full set of actions minimizing that same expected-loss profile. Both constructions compose with the supplied prediction factor map.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Decision/PredictionLawDecisionSufficiency.prediction_law_sufficiency_implies_decision_sufficiency`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
