# Bounded Discussion Blind-Spot Persistence

## Abstract

A discussion that only recombines the agents' joint information cannot resolve a target blind spot of that information.

**Theorem 1.1 (Joint blind spots survive bounded discussion).**

$$\forall I \in Type, X \in Type, B1 \in Type, B2 \in Type, Y \in Type, BM \in I \to Type, C1 \in X \to B1, C2 \in X \to B2, M \in \left(\forall n \in I,\; X \to BM\left(n\right)\right), T \in X \to Y,\; \left(\left(\neg \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(T\right), \operatorname{conceptJoin}\left(C1, C2\right)\right)\right) \land \left(\forall n \in I,\; \operatorname{Refines}\left(M\left(n\right), \operatorname{conceptJoin}\left(C1, C2\right)\right)\right)\right) \Rightarrow \left(\neg \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(T\right), \operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(C1, C2\right), \operatorname{jointReadout}\left(M\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Discussion/BoundedDiscussionBlindSpotPersistence.bounded_discussion_cannot_remove_joint_blind_spot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take two concept readouts and an indexed family of discussion messages. If the canonical target readout does not factor through the agents' joint readout, while every message does factor through it, then the target still does not factor through the join of the agents' readout with all messages.

The indexed message product remains bounded by the original joint readout. Its further join is therefore also bounded by that readout, so target factorization through the extended discussion would contradict the initial blind spot.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Discussion/BoundedDiscussionBlindSpotPersistence.bounded_discussion_cannot_remove_joint_blind_spot`
- Dependency: [D5/S3/ConceptDynamics/Communication/IndexedCommonSourceUpperBound](../Communication/IndexedCommonSourceUpperBound.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/RefinementTransitivity](../Refinement/RefinementTransitivity.md)
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](../Sufficiency/UniversalSufficiencyFactorization.md)
