# Evolution Evidence Pullback Identity

## Abstract

Direct-image evolution after pulled-back evidence equals future conditioning.

**Theorem 1.1 (Evolution after evidence pullback is future conditioning).**

$$\forall X, Y: Type, F: X \to Y, A: \operatorname{Set}\left(X\right), Q: \operatorname{Set}\left(Y\right), \operatorname{image}\left(F, \operatorname{intersection}\left(A, \operatorname{preimage}\left(F, Q\right)\right)\right) = \operatorname{intersection}\left(\operatorname{image}\left(F, A\right), Q\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Revision/EvolutionEvidencePullbackIdentity.evolution_evidence_pullback_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A current state is retained exactly when its future image satisfies the future evidence. Taking the direct image therefore yields precisely the evolved admitted states intersected with that evidence.

The statement is the pinned Mathlib direct-image/intersection/preimage identity, applied without injectivity or surjectivity assumptions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Revision/EvolutionEvidencePullbackIdentity.evolution_evidence_pullback_identity`
