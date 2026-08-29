# Adjudication-Signature Sufficiency and Its Target-Laundering Failure

## Abstract

The four-coordinate adjudication signature preserves non-anticipation, admissible judging, and scientific gain, but not target laundering's whole-commitment report identity.

**Theorem 1.1 (OP1-NA: equal signatures preserve non-anticipation).**

$$\left(\operatorname{adjudicationSignature}\left(Z, L, K, v\right) = \operatorname{adjudicationSignature}\left(Z, R, J, w\right) \land \operatorname{SameOutNA}\left(Z, z\right)\right) \Rightarrow \left(\operatorname{NonAnticipating}\left(K, z\right) \Leftrightarrow \operatorname{NonAnticipating}\left(J, z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureSufficiency.non_anticipating_signature_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a common record in the finite history, equality of the decision-visible, freeze-visible, and directly contaminated coordinates transports each conjunct of NonAnticipating in both directions.

**Theorem 1.2 (OP1-AJ: equal signatures preserve admissible judging).**

$$\left(\operatorname{adjudicationSignature}\left(Z, L, K, v\right) = \operatorname{adjudicationSignature}\left(Z, R, J, w\right) \land \operatorname{SameOutAJ}\left(Z, r\right)\right) \Rightarrow \left(\operatorname{AdmissibleJudge}\left(L, K, v, r\right) \Leftrightarrow \operatorname{AdmissibleJudge}\left(R, J, w, r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureSufficiency.admissible_judge_signature_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fourth coordinate records existence of adjudicate events and of each generate, tune, or select event together with its dependency-closure touch bit. It therefore transports both the positive role requirement and the negated adaptive-contamination requirement.

**Theorem 1.3 (OP1-SG: equal signatures preserve scientific gain).**

$$\left(\operatorname{adjudicationSignature}\left(Z, L, \operatorname{adjudication}\left(K\right), v\right) = \operatorname{adjudicationSignature}\left(Z, R, \operatorname{adjudication}\left(J\right), w\right) \land \operatorname{SameOutSG}\left(Z, z, K, J\right)\right) \Rightarrow \left(\operatorname{ScientificGain}\left(E, K, z, a, b\right) \Leftrightarrow \operatorname{ScientificGain}\left(E, J, z, a, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureSufficiency.scientific_gain_signature_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SameOutSG fixes the committed and baseline action sets and the comparator. The only remaining history-dependent conjunct is NonAnticipating, which is supplied by OP1-NA.

**Theorem 1.4 (OP1-TL: equal signatures do not preserve target laundering).**

$$\exists Z \in \operatorname{Finset}\left(\operatorname{Bool}\left(\right)\right), K \in \operatorname{Commitment}\left(\right), N \in \operatorname{Commitment}\left(\right), J \in \operatorname{Commitment}\left(\right), M \in \operatorname{Commitment}\left(\right), L \in \operatorname{Ledger}\left(\right), R \in \operatorname{Ledger}\left(\right), P \in \operatorname{Ledger}\left(\right), Q \in \operatorname{Ledger}\left(\right), v \in \operatorname{ValidTrace}\left(L, \operatorname{adjudication}\left(K\right)\right), w \in \operatorname{ValidTrace}\left(R, \operatorname{adjudication}\left(N\right)\right), x \in \operatorname{ValidTrace}\left(P, \operatorname{adjudication}\left(J\right)\right), y \in \operatorname{ValidTrace}\left(Q, \operatorname{adjudication}\left(M\right)\right), E \in \operatorname{Commitment}\left(\right) \to \left(\operatorname{Bool}\left(\right) \to \operatorname{Unit}\left(\right)\right), T \in \operatorname{RegradeReport}\left(\operatorname{Commitment}\left(\right), \operatorname{Bool}\left(\right), \operatorname{Unit}\left(\right), \operatorname{Bool}\left(\right), E\right),\; \operatorname{adjudicationSignature}\left(Z, L, \operatorname{adjudication}\left(K\right), v\right) = \operatorname{adjudicationSignature}\left(Z, P, \operatorname{adjudication}\left(J\right), x\right) \land \left(\operatorname{adjudicationSignature}\left(Z, R, \operatorname{adjudication}\left(N\right), w\right) = \operatorname{adjudicationSignature}\left(Z, Q, \operatorname{adjudication}\left(M\right), y\right) \land \left(\operatorname{SameOutTL}\left(Z, true, K, N, J, M\right) \land \left(\operatorname{SketchTargetLaundering}\left(E, K, N, true, T\right) \land \left(\neg \operatorname{SketchTargetLaundering}\left(E, J, M, true, T\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureSufficiency.target_laundering_signature_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite witness uses Boolean event, evidence, artifact, and time types with empty valid role ledgers. The two new commitments differ only in adjudication.frozenAt; all four signature coordinates and all commitment fields outside adjudication are equal.

The common report names the first new commitment as its revised object. SketchTargetLaundering is true on that side, but the same report cannot also name the second, unequal commitment. The omitted frozenAt field separately changes the timestamp identity as well.

SketchTargetLaundering is the frozen Lean name for the no-arrival target-laundering interface used by Part 55; the distinct prose-level TargetLaundering declaration has an additional arrival argument.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureSufficiency.admissible_judge_signature_sufficiency`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureSufficiency.non_anticipating_signature_sufficiency`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureSufficiency.scientific_gain_signature_sufficiency`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureSufficiency.target_laundering_signature_counterexample`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RoleLedgerPrefixStability](../DefinitionEscapeAdjudication/RoleLedgerPrefixStability.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeLaws/ScientificGainGeneralizationReversal](../DefinitionEscapeLaws/ScientificGainGeneralizationReversal.md)
