# Stable and Flip Counterfactual Opposition

## Abstract

Stable and flip models agree on every single-world intervention law while their potential outcomes have opposite couplings.

**Theorem 1.1 (Single-world equivalence with opposite counterfactual coupling).**

$$\begin{gathered}\operatorname{let} S := noEffectModel,\\{}\operatorname{let} F := flipEffectModel,\\{}couplingAgreementProbability\left(S\right) = 1 \land \left(1 - couplingAgreementProbability\left(F\right) = 1 \land \left(\left(\forall a \in PerfectIntervention,\; \forall z \in Bool \times Bool,\; endogenousLaw\left(S, a, z\right) = endogenousLaw\left(F, a, z\right)\right) \land CF\left(S\right) \ne CF\left(F\right)\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InterventionsExchange/StableFlipCounterfactualOpposition.stable_flip_intervention_equivalent_counterfactual_opposite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stable and flip names are bound to the canonical finite Boolean models before any probability or law is stated.

Agreement probability is computed on the same uniform two-unit exogenous population. Its complement is the disagreement probability.

The intervention clause compares the full endogenous joint count law for every perfect intervention on either variable. The final clause compares the unit-preserving counterfactual profiles.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InterventionsExchange/StableFlipCounterfactualOpposition.stable_flip_intervention_equivalent_counterfactual_opposite`
- Dependency: [D5/S3/ConceptDynamics/InterventionLaws/SingleWorldPerfectInterventionLaw](../InterventionLaws/SingleWorldPerfectInterventionLaw.md)
- Dependency: [D5/S3/ConceptDynamics/InterventionsExchange/MarginalTransportCouplingGap](MarginalTransportCouplingGap.md)
