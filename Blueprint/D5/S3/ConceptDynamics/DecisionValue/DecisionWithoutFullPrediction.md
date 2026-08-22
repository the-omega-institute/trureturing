# Decision Sufficiency Without Full Prediction

## Abstract

One constant concept determines every optimal action without determining full payoffs.

**Theorem 1.1 (Decision sufficiency does not require full prediction).**

$$\operatorname{Refines}\left(optimalActions, constantConcept\right) \land \neg \operatorname{Refines}\left(fullPayoffProfile, constantConcept\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValue/DecisionWithoutFullPrediction.decision_sufficiency_without_full_prediction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source has two states and two actions. Action a pays 10 and 100 at the respective states, while action b pays 0 and 1.

The optimal-action concept is constructed as the set of actions whose payoff dominates every alternative. The full-result target records the complete action-payoff profile, and the concept readout is constant.

Both optimal-action sets equal {a}, so the first target factors through the constant concept. The two full profiles differ at action a, so the second target cannot factor through that same concept.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/DecisionWithoutFullPrediction.decision_sufficiency_without_full_prediction`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
