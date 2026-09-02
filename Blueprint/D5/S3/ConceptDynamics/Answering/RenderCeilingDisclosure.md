# Render Ceiling Disclosure

## Abstract

An audited render never exceeds the register ceiling and discloses only the record.

**Theorem 1.1 (Every emitted takeaway is within the register ceiling).**

$$\forall K \in Type, W \in Type, R \in K \to Evidence, w \in W, d \in \operatorname{List}\left(\operatorname{Takeaway}\left(K\right)\right), m \in Disclosure, o \in \operatorname{Output}\left(K, W\right),\; \operatorname{render}\left(R, w, m, d\right) = \operatorname{some}\left(o\right) \Rightarrow \left(\forall t \in \operatorname{Takeaway}\left(K\right),\; t \in \operatorname{prose}\left(o\right) \Rightarrow \operatorname{permits}\left(\operatorname{settle}\left(R\left(\operatorname{key}\left(t\right)\right)\right), \operatorname{claim}\left(t\right)\right) = true\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/RenderCeilingDisclosure.rendered_takeaway_within_ceiling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A draft is a list of competent-reader takeaways, each naming the assertion key it is about and the claim a reader would take away. The register maps each key to the evidence of its unique active record, and the renderer emits the draft only when every takeaway is permitted by the settled outcome of its key.

The theorem fixes the shape of Step 7 of the codex-formal-answer skill. The mapping from prose to takeaways is a worker judgment outside this model; the model guarantees only that whatever the worker maps is bounded by the register.

**Theorem 1.2 (Every emitted formal claim is compiled).**

$$\forall K \in Type, W \in Type, R \in K \to Evidence, w \in W, d \in \operatorname{List}\left(\operatorname{Takeaway}\left(K\right)\right), m \in Disclosure, o \in \operatorname{Output}\left(K, W\right),\; \operatorname{render}\left(R, w, m, d\right) = \operatorname{some}\left(o\right) \Rightarrow \left(\forall t \in \operatorname{Takeaway}\left(K\right),\; \left(t \in \operatorname{prose}\left(o\right) \land \operatorname{isFormal}\left(\operatorname{claim}\left(t\right)\right) = true\right) \Rightarrow \operatorname{buildSucceeded}\left(R\left(\operatorname{key}\left(t\right)\right)\right) = true\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/RenderCeilingDisclosure.rendered_formal_claim_is_compiled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Composing the audit with ceiling soundness: any formal-grade claim that an emitted answer conveys about an assertion is backed by one successful current build of the exact statement it is about. Search hits, prose synthesis, and unbuilt proof texts cannot reach the reader as formal claims.

**Lemma 1.3 (An open assertion blocks emission).**

$$\forall K \in Type, W \in Type, R \in K \to Evidence, w \in W, d \in \operatorname{List}\left(\operatorname{Takeaway}\left(K\right)\right), m \in Disclosure, t \in \operatorname{Takeaway}\left(K\right),\; \left(t \in d \land \left(\operatorname{settle}\left(R\left(\operatorname{key}\left(t\right)\right)\right) = open \land \operatorname{claim}\left(t\right) \ne unsettled\right)\right) \Rightarrow \operatorname{render}\left(R, w, m, d\right) = none$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/RenderCeilingDisclosure.open_key_blocks_emission` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If any takeaway conveys more than the unsettled claim about an open assertion, the audit fails and nothing is emitted in either disclosure mode. An open assertion may be reported only as unsettled, never as P, its negation, or a conditional consequent.

**Theorem 1.4 (Disclosure changes the attachment, not the claims).**

$$\forall K \in Type, W \in Type, R \in K \to Evidence, w \in W, d \in \operatorname{List}\left(\operatorname{Takeaway}\left(K\right)\right),\; \operatorname{map}\left(prose, \operatorname{render}\left(R, w, plain, d\right)\right) = \operatorname{map}\left(prose, \operatorname{render}\left(R, w, showWork, d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/RenderCeilingDisclosure.disclosure_preserves_claims` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The plain answer and the show-work answer pass the same audit and carry the same prose; the disclosure switch decides only whether the internal run record is attached. Asking to see the reasoning therefore never strengthens or weakens what the answer claims.

**Lemma 1.5 (Show-work attaches the record).**

$$\forall K \in Type, W \in Type, R \in K \to Evidence, w \in W, d \in \operatorname{List}\left(\operatorname{Takeaway}\left(K\right)\right), o \in \operatorname{Output}\left(K, W\right),\; \operatorname{render}\left(R, w, showWork, d\right) = \operatorname{some}\left(o\right) \Rightarrow \operatorname{record}\left(o\right) = \operatorname{some}\left(w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/RenderCeilingDisclosure.show_work_exposes_record` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In show-work mode an emitted answer carries the internal record, and the companion lemma for plain mode shows it carries none. What is disclosed is the record itself, not a fresh narrative about it.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Answering/RenderCeilingDisclosure.disclosure_preserves_claims`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/RenderCeilingDisclosure.open_key_blocks_emission`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/RenderCeilingDisclosure.rendered_formal_claim_is_compiled`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/RenderCeilingDisclosure.rendered_takeaway_within_ceiling`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/RenderCeilingDisclosure.show_work_exposes_record`
- Dependency: [D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling](AssertionSettlementCeiling.md)
