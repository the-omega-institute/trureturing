# Intervention-Counterfactual Separation

## Abstract

Two Boolean causal models can agree on every interventional marginal while disagreeing on a unit-level counterfactual.

**Theorem 1.1 (Interventional marginals do not determine counterfactuals).**

$$\exists M, N: DeterministicBoolSCM, \operatorname{Int}\left(M\right) = \operatorname{Int}\left(N\right) \land \operatorname{CF}\left(M\right) \ne \operatorname{CF}\left(N\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A deterministic Boolean causal model assigns an outcome to each exogenous unit and imposed treatment. Its interventional marginal counts outcomes over the uniform two-unit exogenous population, whereas its counterfactual retains the unit while replacing the treatment.

The first witness ignores treatment and returns the exogenous bit. The second preserves that bit under false treatment and complements it under true treatment. For either treatment, each model produces one false outcome and one true outcome, so all interventional counts agree.

For the false exogenous unit with true as the alternate treatment, the first model returns false and the second returns true. Their unit-level counterfactual functions therefore differ despite identical interventional marginals.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interventions/InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual`
