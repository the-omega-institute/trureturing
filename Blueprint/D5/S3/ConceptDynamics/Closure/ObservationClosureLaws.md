# Observation Closure Laws

## Abstract

Observation closure has the three closure laws and adds no distinctions.

**Theorem 1.1 (Observation closure is extensive, monotone, idempotent, and redundant).**

$$\forall X \in Type, O \in Type, Q \in \operatorname{Set}\left(\operatorname{Concept}\left(X, O\right)\right), Q2 \in \operatorname{Set}\left(\operatorname{Concept}\left(X, O\right)\right),\; Q \subseteq \operatorname{DefinitionClosure}\left(Q\right) \land \left(\left(Q \subseteq Q2 \Rightarrow \operatorname{DefinitionClosure}\left(Q\right) \subseteq \operatorname{DefinitionClosure}\left(Q2\right)\right) \land \left(\operatorname{DefinitionClosure}\left(\operatorname{DefinitionClosure}\left(Q\right)\right) = \operatorname{DefinitionClosure}\left(Q\right) \land \left(\forall p \in \operatorname{Concept}\left(X, O\right),\; p \in \operatorname{DefinitionClosure}\left(Q\right) \Rightarrow \operatorname{jointKernel}\left(\lambda q: \operatorname{insert}\left(p, Q\right), \operatorname{val}\left(q\right)\right) = \operatorname{jointKernel}\left(\lambda q: Q, \operatorname{val}\left(q\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Closure/ObservationClosureLaws.observation_closure_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

DefinitionClosure is the canonical source-semantic closure constructed from the common observational kernel. The first three public clauses are its extensive, monotone, and idempotent laws.

The final public clause quantifies over every candidate in the closure. Inserting such a readout leaves the canonical joint kernel unchanged, so it cannot split a state pair left indistinguishable by the source family.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Closure/ObservationClosureLaws.observation_closure_laws`
- Dependency: [D5/S3/ConceptDynamics/Closure/SourceClosureThreeLaws](SourceClosureThreeLaws.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeLaws/SemanticClosureZeroGainCriterion](../DefinitionEscapeLaws/SemanticClosureZeroGainCriterion.md)
