# Source-Bounded Paraphrases Preserve Target Blind Spots

## Abstract

Any indexed family of paraphrases bounded by a common source preserves that source's target blind spot.

**Theorem 1.1 (Source-bounded paraphrases preserve a target blind spot).**

$$\forall I \in Type, X \in Type, M \in I \to Type, B \in Type, Y \in Type, p \in \left(\forall i \in I,\; X \to M\left(i\right)\right), S \in X \to B, T \in X \to Y,\; \left(\left(\neg \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(T\right), S\right)\right) \land \left(\forall i \in I,\; \operatorname{Refines}\left(p\left(i\right), S\right)\right)\right) \Rightarrow \left(\neg \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(T\right), \operatorname{jointReadout}\left(p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Discussion/SourceBoundedParaphraseBlindSpot.source_bounded_paraphrases_preserve_target_blind_spot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source, target, and dependent indexed family of paraphrase readouts are arbitrary. The public premises say that the source cannot decide the target and that every paraphrase factors through the source.

The canonical joint readout of the entire paraphrase family still factors through the source. If it decided the target, refinement transitivity would make the target decidable from the source, contradicting the initial blind spot.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Discussion/SourceBoundedParaphraseBlindSpot.source_bounded_paraphrases_preserve_target_blind_spot`
- Dependency: [D5/S3/ConceptDynamics/Communication/IndexedCommonSourceUpperBound](../Communication/IndexedCommonSourceUpperBound.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/RefinementTransitivity](../Refinement/RefinementTransitivity.md)
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](../Sufficiency/UniversalSufficiencyFactorization.md)
