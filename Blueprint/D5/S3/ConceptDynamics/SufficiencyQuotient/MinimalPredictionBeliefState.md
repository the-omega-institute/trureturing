# Minimal Prediction Belief State

## Abstract

Every summary sufficient for all future observation profiles maps uniquely and surjectively onto the predictive belief quotient.

**Theorem 1.1 (The predictive quotient is the minimal empirical history state).**

$$\forall History \in \operatorname{Type}\left(\right), Query \in \operatorname{Type}\left(\right), Summary \in \operatorname{Type}\left(\right), Observation \in Query \to \operatorname{Type}\left(\right), possibleObservation \in \forall q: Query, History \to Observation\left(q\right), summary \in History \to Summary, predictor \in Summary \to \forall q: Query, Observation\left(q\right),\; \operatorname{jointReadout}\left(possibleObservation\right) = \operatorname{compose}\left(predictor, summary\right) \Rightarrow \left(\left(\forall h \in History, hPrime \in History,\; summary\left(h\right) = summary\left(hPrime\right) \Rightarrow \left(\operatorname{quotientClass}\left(\operatorname{jointReadout}\left(possibleObservation\right), h\right) = \operatorname{quotientClass}\left(\operatorname{jointReadout}\left(possibleObservation\right), hPrime\right) \land \left(\forall Objective \in \operatorname{Type}\left(\right), g \in \forall q: Query, Observation\left(q\right) \to Objective,\; g\left(\operatorname{jointReadout}\left(possibleObservation\right)\left(h\right)\right) = g\left(\operatorname{jointReadout}\left(possibleObservation\right)\left(hPrime\right)\right)\right)\right)\right) \land \exists! factor: \operatorname{range}\left(summary\right) \to \operatorname{Quotient}\left(\operatorname{ker}\left(\operatorname{jointReadout}\left(possibleObservation\right)\right)\right), \operatorname{quotientClassMap}\left(\operatorname{jointReadout}\left(possibleObservation\right)\right) = \operatorname{compose}\left(factor, \operatorname{rangeFactorization}\left(summary\right)\right) \land \operatorname{Surjective}\left(factor\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SufficiencyQuotient/MinimalPredictionBeliefState.minimal_prediction_belief_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is an arbitrary history type with a dependent family of possible-observation readouts indexed by every future query. The canonical jointReadout forms the complete predictive profile; no second profile primitive is introduced.

A predictor through the summary is the public sufficiency premise. Equal summary values therefore give equal kernel-quotient classes and equal values for every empirical objective computed from the complete observation profile.

The factor starts at the realized image of the possibly redundant summary and ends at the named quotient by predictive equivalence. Its public factorization, surjectivity, and uniqueness express the minimality distinction from raw history and redundant summaries.

The proof applies the frozen causal-state image factorization and the pinned-library quotient-kernel equivalence. No exact existing theorem included the quotient, objective, and unrestricted empty-history clauses together.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SufficiencyQuotient/MinimalPredictionBeliefState.minimal_prediction_belief_state`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
- Dependency: [D5/S3/ObserverMemory/PredictionFactors/CausalStateFactorization](../../ObserverMemory/PredictionFactors/CausalStateFactorization.md)
