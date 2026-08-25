# Marginal Transport and Coupling

## Abstract

Equal single-world intervention marginals can transport while cross-world agreement changes.

**Theorem 1.1 (Marginal transport does not determine coupling transport).**

$$\operatorname{Int}\left(noEffectModel\right) = \operatorname{Int}\left(flipEffectModel\right) \land \operatorname{couplingAgreementProbability}\left(noEffectModel\right) \ne \operatorname{couplingAgreementProbability}\left(flipEffectModel\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InterventionsExchange/MarginalTransportCouplingGap.marginal_transport_does_not_determine_coupling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stable model returns the exogenous bit under both treatments. The flip model preserves it under false treatment and complements it under true treatment.

Both models therefore have one false and one true outcome under each single-world intervention. Their intervention-count tables coincide.

The coupling query uses the same uniform two-unit exogenous population. The two potential outcomes always agree in the stable model and never agree in the flip model, so the agreement probabilities differ.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InterventionsExchange/MarginalTransportCouplingGap.marginal_transport_does_not_determine_coupling`
- Dependency: [D5/S3/ConceptDynamics/Interventions/InterventionCounterfactualSeparation](../Interventions/InterventionCounterfactualSeparation.md)
