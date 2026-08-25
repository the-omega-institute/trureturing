# Finite Intervention Extraction

## Abstract

A separating intervention family on a finite model class has a finite separating subfamily.

**Theorem 1.1 (Finitely many interventions retain all target distinctions).**

$$\forall n \in \mathbb{N},\ Intervention, Response, Target: \operatorname{Type},\ readout: Intervention \to (\operatorname{Fin}\left(n\right) \to Response),\ target: \operatorname{Fin}\left(n\right) \to Target,\ (\forall i, j: \operatorname{Fin}\left(n\right), \operatorname{target}\left(i\right) \neq \operatorname{target}\left(j\right) \Rightarrow \exists a: Intervention, \operatorname{readout}\left(a, i\right) \neq \operatorname{readout}\left(a, j\right)) \Rightarrow \exists J: \operatorname{Set}\left(Intervention\right),\ \operatorname{Finite}\left(J\right) \land \forall i, j: \operatorname{Fin}\left(n\right), \operatorname{target}\left(i\right) \neq \operatorname{target}\left(j\right) \Rightarrow \exists a: Intervention, a \in J \land \operatorname{readout}\left(a, i\right) \neq \operatorname{readout}\left(a, j\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/FiniteInterventionExtraction.finite_intervention_extraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The relevant universe consists of unordered pairs of finite models whose target values differ. The assumed intervention family covers this finite universe by its separation sets.

A finite subcover therefore selects finitely many allowed interventions. Every target-distinct model pair is still separated by at least one selected intervention.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/FiniteInterventionExtraction.finite_intervention_extraction`
- Dependency: [D5/S3/ConceptDynamics/Interventions/TargetRelativePairUniverse](../Interventions/TargetRelativePairUniverse.md)
