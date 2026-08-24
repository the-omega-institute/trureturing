# Conflicting Evidence Aggregation

## Abstract

Negative support joins true-only evidence into a both-supported conflict state.

**Theorem 1.1 (Negative evidence moves true-only support to both).**

$$\forall e: \operatorname{EvidenceValue}, e_{neg} = true \Rightarrow\\{}(\operatorname{aggregateEvidence}\left(\mathbf{T}, e\right) = \mathbf{B}) \land\\{}(\operatorname{InformationLe}\left(\mathbf{T}, \operatorname{aggregateEvidence}\left(\mathbf{T}, e\right)\right) \land \operatorname{InformationLe}\left(e, \operatorname{aggregateEvidence}\left(\mathbf{T}, e\right)\right) \land \mathbf{T} \neq \operatorname{aggregateEvidence}\left(\mathbf{T}, e\right)) \land\\{}(\operatorname{EvidenceConsistent}\left(\mathbf{T}\right) \land \neg \operatorname{EvidenceConsistent}\left(\operatorname{aggregateEvidence}\left(\mathbf{T}, e\right)\right)) \land\\{}(\operatorname{aggregateEvidence}\left(\mathbf{T}, e\right)_{pos} = true \land \operatorname{aggregateEvidence}\left(\mathbf{T}, e\right)_{neg} = true).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Evidence/ConflictingEvidenceAggregation.negative_evidence_moves_true_only_to_both` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An evidence value is the source pair of positive and negative support bits. Aggregation applies Boolean disjunction in each coordinate, so support recorded by either source is retained.

Start from the canonical true-only value and add any source whose negative support bit is set. The aggregate is the canonical both-supported value, lies above both inputs in the componentwise information order, and is strictly above the true-only input.

True-only evidence is consistent because one polarity is absent. The aggregate has both support bits, so it is inconsistent precisely by exposing the two sources' conflict, not by discarding information.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Evidence/ConflictingEvidenceAggregation.negative_evidence_moves_true_only_to_both`
- Dependency: [D5/S3/ConceptDynamics/Evidence/EvidenceFourPhaseLaw](EvidenceFourPhaseLaw.md)
