# Assertion Settlement Ceiling

## Abstract

First-match settlement of an assertion record bounds its permitted public claim.

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

This is ceiling soundness for the answer register: whatever formal claim the maximum permitted claim licenses, one successful current build of the exact statement stands behind it. It says nothing about claims a renderer might convey outside the register; that gap is closed by the audited renderer.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.failed_build_settles_open_or_not_formalized`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.formal_claim_requires_successful_build`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.not_formalized_independent_of_build`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.open_permits_only_unsettled`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.settle_first_match`
