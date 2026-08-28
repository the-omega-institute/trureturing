# Single-World Intervention-Law Agreement

## Abstract

The stable and flip Boolean models agree under every perfect single-world intervention.

**Theorem 1.1 (All perfect single-world intervention laws agree).**

$$\begin{gathered}\operatorname{let} S := noEffectModel,\\{}\operatorname{let} F := flipEffectModel,\\{}\left(\forall x \in Bool,\; \forall y \in Bool,\; Int\left(S, x, y\right) = 1 \land Int\left(F, x, y\right) = 1\right) \land \left(\forall a \in PerfectIntervention,\; \forall z \in Bool \times Bool,\; endogenousLaw\left(S, a, z\right) = endogenousLaw\left(F, a, z\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InterventionsExchange/SingleWorldInterventionLawAgreement.single_world_perfect_intervention_laws_agree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement binds S to noEffectModel and F to flipEffectModel before either law is mentioned. Neither model identifier is free.

For each imposed treatment, both models give one occurrence of each Boolean outcome over the uniform exogenous population.

The second clause compares the complete endogenous joint count law under every perfect intervention. The intervention type includes operations fixing X and operations fixing Y.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InterventionsExchange/SingleWorldInterventionLawAgreement.single_world_perfect_intervention_laws_agree`
- Dependency: [D5/S3/ConceptDynamics/InterventionLaws/SingleWorldPerfectInterventionLaw](../InterventionLaws/SingleWorldPerfectInterventionLaw.md)
