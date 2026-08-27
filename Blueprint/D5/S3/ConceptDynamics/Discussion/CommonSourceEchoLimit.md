# Common-Source Echo Limit

## Abstract

Messages derived from one common source cannot resolve a target blind to that source.

**Theorem 1.1 (Common-source repetition cannot resolve a blind target).**

$$\forall I \in Type, X \in Type, B \in Type, Y \in Type, BM \in I \to Type, S \in X \to B, M \in \left(\forall i \in I,\; X \to BM\left(i\right)\right), T \in X \to Y,\; \left(\neg \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(T\right), S\right)\right) \Rightarrow \left(\left(\left(\forall i \in I,\; \operatorname{Refines}\left(M\left(i\right), S\right)\right) \Rightarrow \left(\neg \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(T\right), \operatorname{jointReadout}\left(M\right)\right)\right)\right) \land \left(\operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(T\right), \operatorname{jointReadout}\left(M\right)\right) \Rightarrow \left(\exists i \in I,\; \neg \operatorname{Refines}\left(M\left(i\right), S\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Discussion/CommonSourceEchoLimit.common_source_repetition_cannot_resolve_blind_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take an arbitrary indexed family of messages. If every message factors through the same source readout, their canonical joint readout also factors through that source and cannot determine a target that the source does not determine.

Consequently, if the joint message readout does determine the target, at least one component message must introduce a distinction that does not factor through the common source.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Discussion/CommonSourceEchoLimit.common_source_repetition_cannot_resolve_blind_target`
- Dependency: [D5/S3/ConceptDynamics/Communication/IndexedCommonSourceUpperBound](../Communication/IndexedCommonSourceUpperBound.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/RefinementTransitivity](../Refinement/RefinementTransitivity.md)
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](../Sufficiency/UniversalSufficiencyFactorization.md)
