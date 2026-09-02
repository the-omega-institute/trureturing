# Assertion Settlement Ceiling

## Abstract

First-match settlement of an assertion record bounds its permitted public claim, and an audited render never exceeds that ceiling while disclosing only the record.

**Theorem 1.1 (First-match settlement is exhaustive and single-valued).**

$$\forall e \in Evidence,\; \left(\operatorname{settle}\left(e\right) = notFormalized \Leftrightarrow \operatorname{notFormalizedRule}\left(e\right) = true\right) \land \left(\left(\operatorname{settle}\left(e\right) = conditional \Leftrightarrow \left(\operatorname{notFormalizedRule}\left(e\right) = false \land \left(\operatorname{compiledP}\left(e\right) = true \land 0 < \operatorname{undischarged}\left(e\right)\right)\right)\right) \land \left(\left(\operatorname{settle}\left(e\right) = proved \Leftrightarrow \left(\operatorname{notFormalizedRule}\left(e\right) = false \land \left(\operatorname{compiledP}\left(e\right) = true \land \operatorname{undischarged}\left(e\right) = 0\right)\right)\right) \land \left(\left(\operatorname{settle}\left(e\right) = refuted \Leftrightarrow \left(\operatorname{notFormalizedRule}\left(e\right) = false \land \left(\operatorname{compiledP}\left(e\right) = false \land \operatorname{compiledNegP}\left(e\right) = true\right)\right)\right) \land \left(\operatorname{settle}\left(e\right) = open \Leftrightarrow \left(\operatorname{notFormalizedRule}\left(e\right) = false \land \left(\operatorname{compiledP}\left(e\right) = false \land \operatorname{compiledNegP}\left(e\right) = false\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.settle_first_match` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An assertion record carries a clause-shape classification fixed at inventory time, whether a Lean statement exists, whether one current canonical build succeeded, whether the compiled statement is exact P or its exact negation, and how many named empirical or metaphysical premises remain undischarged.

Settlement applies five ordered rules: not-formalized for a not-formalizable record without a Lean statement, conditional for compiled P with an undischarged premise, proved for compiled P with none, refuted for a compiled negation, and open otherwise. Each outcome is characterized exactly by the first rule it matches, so every record receives one outcome and no record receives two.

This is the formal shape of Step 5 of the codex-formal-answer skill. It fixes how evidence maps to an outcome; it does not decide whether any particular Lean statement is the user's P, which remains the statement-echo judgment of Step 3.

**Lemma 1.2 (A failed build settles nothing).**

$$\forall e \in Evidence,\; \operatorname{buildSucceeded}\left(e\right) = false \Rightarrow \left(\operatorname{settle}\left(e\right) = open \lor \operatorname{settle}\left(e\right) = notFormalized\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.failed_build_settles_open_or_not_formalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both compiled-P and compiled-negation conditions require a successful build, so a failed or unavailable build can only reach the open rule or the earlier not-formalized rule. A proof text that did not compile therefore neither proves nor refutes anything.

**Lemma 1.3 (Formalizability is independent of the build).**

$$\forall e \in Evidence, f \in Evidence,\; \left(\operatorname{classification}\left(e\right) = \operatorname{classification}\left(f\right) \land \operatorname{hasLeanStatement}\left(e\right) = \operatorname{hasLeanStatement}\left(f\right)\right) \Rightarrow \left(\operatorname{settle}\left(e\right) = notFormalized \Leftrightarrow \operatorname{settle}\left(f\right) = notFormalized\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.not_formalized_independent_of_build` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two records with the same classification and the same statement presence settle not-formalized together, whatever their build and proof fields. Capability failure, proof difficulty, and elapsed effort cannot reclassify a clause.

**Lemma 1.4 (An open record permits only the unsettled claim).**

$$\forall c \in Claim,\; \operatorname{permits}\left(open, c\right) = true \Leftrightarrow c = unsettled$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.open_permits_only_unsettled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Claims are ordered by commitment: the unsettled claim conveys nothing about P, the conditional consequent lies below exact P, and other claims compare only with themselves. The open outcome has the unsettled claim as its ceiling, so it permits neither P, nor its negation, nor a conditional consequent.

**Theorem 1.5 (A permitted formal claim is backed by a successful build).**

$$\forall e \in Evidence, c \in Claim,\; \left(\operatorname{isFormal}\left(c\right) = true \land \operatorname{permits}\left(\operatorname{settle}\left(e\right), c\right) = true\right) \Rightarrow \operatorname{buildSucceeded}\left(e\right) = true$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.formal_claim_requires_successful_build` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only the proved, refuted, and conditional outcomes permit a formal-grade claim, and each of those outcomes is characterized by a compiled statement, which requires a successful build.

This is ceiling soundness for the answer register: whatever formal claim the maximum permitted claim licenses, one successful current build of the exact statement stands behind it. It says nothing about claims a renderer might convey outside the register; that gap is closed by the audited renderer below.

**Theorem 1.6 (Every emitted takeaway is within the register ceiling).**

$$\forall K \in Type, W \in Type, R \in K \to Evidence, w \in W, d \in \operatorname{List}\left(\operatorname{Takeaway}\left(K\right)\right), m \in Disclosure, o \in \operatorname{Output}\left(K, W\right),\; \operatorname{render}\left(R, w, m, d\right) = \operatorname{some}\left(o\right) \Rightarrow \left(\forall t \in \operatorname{Takeaway}\left(K\right),\; t \in \operatorname{prose}\left(o\right) \Rightarrow \operatorname{permits}\left(\operatorname{settle}\left(R\left(\operatorname{key}\left(t\right)\right)\right), \operatorname{claim}\left(t\right)\right) = true\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.rendered_takeaway_within_ceiling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A draft is a list of competent-reader takeaways, each naming the assertion key it is about and the claim a reader would take away. The register maps each key to the evidence of its unique active record, and the renderer emits the draft only when every takeaway is permitted by the settled outcome of its key.

The theorem fixes the shape of Step 7 of the codex-formal-answer skill. The mapping from prose to takeaways is a worker judgment outside this model; the model guarantees only that whatever the worker maps is bounded by the register.

**Theorem 1.7 (Every emitted formal claim is compiled).**

$$\forall K \in Type, W \in Type, R \in K \to Evidence, w \in W, d \in \operatorname{List}\left(\operatorname{Takeaway}\left(K\right)\right), m \in Disclosure, o \in \operatorname{Output}\left(K, W\right),\; \operatorname{render}\left(R, w, m, d\right) = \operatorname{some}\left(o\right) \Rightarrow \left(\forall t \in \operatorname{Takeaway}\left(K\right),\; \left(t \in \operatorname{prose}\left(o\right) \land \operatorname{isFormal}\left(\operatorname{claim}\left(t\right)\right) = true\right) \Rightarrow \operatorname{buildSucceeded}\left(R\left(\operatorname{key}\left(t\right)\right)\right) = true\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.rendered_formal_claim_is_compiled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Composing the audit with ceiling soundness: any formal-grade claim that an emitted answer conveys about an assertion is backed by one successful current build of the exact statement it is about. Search hits, prose synthesis, and unbuilt proof texts cannot reach the reader as formal claims.

**Lemma 1.8 (An open assertion blocks emission).**

$$\forall K \in Type, W \in Type, R \in K \to Evidence, w \in W, d \in \operatorname{List}\left(\operatorname{Takeaway}\left(K\right)\right), m \in Disclosure, t \in \operatorname{Takeaway}\left(K\right),\; \left(t \in d \land \left(\operatorname{settle}\left(R\left(\operatorname{key}\left(t\right)\right)\right) = open \land \operatorname{claim}\left(t\right) \ne unsettled\right)\right) \Rightarrow \operatorname{render}\left(R, w, m, d\right) = none$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.open_key_blocks_emission` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If any takeaway conveys more than the unsettled claim about an open assertion, the audit fails and nothing is emitted in either disclosure mode. An open assertion may be reported only as unsettled, never as P, its negation, or a conditional consequent.

**Theorem 1.9 (Disclosure changes the attachment, not the claims).**

$$\forall K \in Type, W \in Type, R \in K \to Evidence, w \in W, d \in \operatorname{List}\left(\operatorname{Takeaway}\left(K\right)\right),\; \operatorname{map}\left(prose, \operatorname{render}\left(R, w, plain, d\right)\right) = \operatorname{map}\left(prose, \operatorname{render}\left(R, w, showWork, d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.disclosure_preserves_claims` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The plain answer and the show-work answer pass the same audit and carry the same prose; the disclosure switch decides only whether the internal run record is attached. Asking to see the reasoning therefore never strengthens or weakens what the answer claims.

**Lemma 1.10 (Show-work attaches the record).**

$$\forall K \in Type, W \in Type, R \in K \to Evidence, w \in W, d \in \operatorname{List}\left(\operatorname{Takeaway}\left(K\right)\right), o \in \operatorname{Output}\left(K, W\right),\; \operatorname{render}\left(R, w, showWork, d\right) = \operatorname{some}\left(o\right) \Rightarrow \operatorname{record}\left(o\right) = \operatorname{some}\left(w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.show_work_exposes_record` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In show-work mode an emitted answer carries the internal record, and the companion lemma for plain mode shows it carries none. What is disclosed is the record itself, not a fresh narrative about it.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.disclosure_preserves_claims`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.failed_build_settles_open_or_not_formalized`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.formal_claim_requires_successful_build`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.not_formalized_independent_of_build`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.open_key_blocks_emission`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.open_permits_only_unsettled`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.rendered_formal_claim_is_compiled`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.rendered_takeaway_within_ceiling`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.settle_first_match`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.show_work_exposes_record`
