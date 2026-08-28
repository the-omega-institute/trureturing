# Single-World Perfect-Intervention Laws

## Abstract

The stable and flip Boolean SCMs agree under every single-world perfect intervention.

**Theorem 1.1 (All single-world perfect-intervention laws agree).**

$$\begin{gathered}(\forall x, y: Bool, \operatorname{Int}\left(S, x, y\right) = 1 \land \operatorname{Int}\left(F, x, y\right) = 1)\\{}\land\\{}(\forall a: PerfectIntervention, z: Bool \times Bool, \operatorname{endogenousLaw}\left(S, a, z\right) = \operatorname{endogenousLaw}\left(F, a, z\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InterventionLaws/SingleWorldPerfectInterventionLaw.all_single_world_perfect_intervention_laws_agree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stable model returns the exogenous unit, while the flip model complements it exactly when the imposed treatment is true. The treatment-intervention marginal counts both values of the uniform exogenous unit.

A perfect intervention fixes either X or Y. The endogenous joint count law is constructed by evaluating the remaining structural equation over the four equally weighted pairs of independent Boolean exogenous coordinates.

The first public clause gives count one to each potential outcome in both models. The second compares the complete endogenous joint count law for every intervention, so interventions fixing Y are included.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InterventionLaws/SingleWorldPerfectInterventionLaw.all_single_world_perfect_intervention_laws_agree`
- Dependency: [D5/S3/ConceptDynamics/Interventions/InterventionCounterfactualSeparation](../Interventions/InterventionCounterfactualSeparation.md)
