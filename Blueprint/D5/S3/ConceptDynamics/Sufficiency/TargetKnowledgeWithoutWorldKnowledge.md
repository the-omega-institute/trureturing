# Target Knowledge Without World Knowledge

## Abstract

A target-sufficient concept need not determine the complete world state.

**Lemma 1.1 (The first coordinate is sufficient but incomplete).**

$$\begin{gathered}X = \operatorname{Bool} \times \operatorname{Bool},\\{}T = C = \operatorname{fst}, W = \operatorname{id},\\{}\operatorname{Refines}(\operatorname{canonicalTargetReadout}(T), C) \land \neg \operatorname{ConceptEquivalent}(C, W).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/TargetKnowledgeWithoutWorldKnowledge.answer_concept_sufficient_but_incomplete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a world to be a pair of Boolean coordinates. The target and the answer concept both read the first coordinate, so the canonical target-image readout factors through that concept.

The concept is not equivalent to complete world knowledge. It identifies the worlds (false, false) and (false, true), while the identity readout distinguishes them, so no reverse factor can recover the second coordinate.

**Theorem 1.2 (Target knowledge does not require world knowledge).**

$$\begin{gathered}\exists X, Target, Coordinate: \operatorname{Type},\\{}T: X \to Target, C: X \to Coordinate,\\{}\operatorname{Refines}(\operatorname{canonicalTargetReadout}(T), C) \land \neg \operatorname{ConceptEquivalent}(C, id_{X}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/TargetKnowledgeWithoutWorldKnowledge.target_knowledge_without_world_knowledge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exist a state space, a target readout, and a concept from which the canonical target answer can be recovered even though the concept is not equivalent to the identity readout on states.

The Boolean-pair construction supplies the witness: retain the first bit needed by the target and discard the independent second bit. Thus target sufficiency is strictly weaker than complete world recovery.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/TargetKnowledgeWithoutWorldKnowledge.answer_concept_sufficient_but_incomplete`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/TargetKnowledgeWithoutWorldKnowledge.target_knowledge_without_world_knowledge`
- Dependency: [D5/S3/ConceptDynamics/Interventions/RedundantAppealDefectPersistence](../Interventions/RedundantAppealDefectPersistence.md)
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](UniversalSufficiencyFactorization.md)
