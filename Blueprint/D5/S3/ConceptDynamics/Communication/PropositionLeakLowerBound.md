# Proposition Leak Lower Bound

## Abstract

A transcript deciding a nonconstant Boolean proposition must reveal a distinction, and the proposition itself realizes exact leakage.

**Theorem 1.1 (A nonconstant proposition forces a transcript distinction).**

$$\forall Secret \in Type, Transcript \in Type, transcript \in Secret \to Transcript, Q \in Secret \to Bool,\; \left(\operatorname{ProvesProposition}\left(transcript, Q\right) \land \left(\exists s1 \in Secret, s2 \in Secret,\; Q\left(s1\right) \ne Q\left(s2\right)\right)\right) \Rightarrow \left(\exists s1 \in Secret, s2 \in Secret,\; transcript\left(s1\right) \ne transcript\left(s2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Communication/PropositionLeakLowerBound.transcript_leaks_at_least_the_proposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose a deterministic decoder recovers a Boolean proposition from the transcript, and two secret states have different proposition values. If those states had the same transcript, the decoder would give them the same value, contradicting nonconstancy.

Consequently the transcript must separate at least one pair already separated by the proposition. In particular, no constant transcript can decide a nonconstant proposition.

**Lemma 1.2 (The proposition itself is an exact transcript).**

$$\forall Secret \in Type, Q \in Secret \to Bool,\; \exists transcript \in Secret \to Bool,\; \operatorname{LeaksExactlyProposition}\left(transcript, Q\right) \land \operatorname{ProvesProposition}\left(transcript, Q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Communication/PropositionLeakLowerBound.proposition_only_transcript_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Boolean proposition, use its truth value as the transcript. Two states then have equal transcripts exactly when they have equal proposition values, and the identity decoder recovers the proposition. Thus the lower bound is attained without revealing any finer distinction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Communication/PropositionLeakLowerBound.proposition_only_transcript_exists`
- Truth anchor: `D5/S3/ConceptDynamics/Communication/PropositionLeakLowerBound.transcript_leaks_at_least_the_proposition`
- Dependency: [D5/S0/Rewriting/Quotients/AnswerabilityCriterion](../../../S0/Rewriting/Quotients/AnswerabilityCriterion.md)
