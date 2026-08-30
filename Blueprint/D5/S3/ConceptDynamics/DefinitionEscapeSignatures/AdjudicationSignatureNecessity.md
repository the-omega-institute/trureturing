# Coordinate Necessity of the Adjudication Signature

## Abstract

Every coordinate of the sufficient adjudication signature has a finite deletion witness among the post-OP1 surviving consumers.

**Definition 1.1 (Freeze-visibility deletion witness).**

$$\operatorname{let} positive = \operatorname{adjudicationSignature}\left(records, emptyLedger, clean, \operatorname{emptyValid}\left(clean\right)\right), \operatorname{let} negative = \operatorname{adjudicationSignature}\left(records, emptyLedger, freezeExposed, \operatorname{emptyValid}\left(freezeExposed\right)\right), \operatorname{SameOutNA}\left(records, true\right) \land \left(\operatorname{decisionVisible}\left(positive\right) = \operatorname{decisionVisible}\left(negative\right) \land \left(\operatorname{directlyContaminated}\left(positive\right) = \operatorname{directlyContaminated}\left(negative\right) \land \left(\operatorname{roleProjection}\left(positive\right) = \operatorname{roleProjection}\left(negative\right) \land \left(\operatorname{freezeVisible}\left(positive\right) \ne \operatorname{freezeVisible}\left(negative\right) \land \left(\operatorname{NonAnticipating}\left(clean, true\right) \Leftrightarrow \left(\neg \operatorname{NonAnticipating}\left(freezeExposed, true\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureNecessity.FreezeVisibilityDirection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NonAnticipating is true when evidence first appears at decision and false when the same evidence is already visible at freeze.

**Definition 1.2 (Decision-visibility deletion witness).**

$$\operatorname{let} positive = \operatorname{adjudicationSignature}\left(records, emptyLedger, clean, \operatorname{emptyValid}\left(clean\right)\right), \operatorname{let} negative = \operatorname{adjudicationSignature}\left(records, emptyLedger, decisionHidden, \operatorname{emptyValid}\left(decisionHidden\right)\right), \operatorname{SameOutNA}\left(records, true\right) \land \left(\operatorname{freezeVisible}\left(positive\right) = \operatorname{freezeVisible}\left(negative\right) \land \left(\operatorname{directlyContaminated}\left(positive\right) = \operatorname{directlyContaminated}\left(negative\right) \land \left(\operatorname{roleProjection}\left(positive\right) = \operatorname{roleProjection}\left(negative\right) \land \left(\operatorname{decisionVisible}\left(positive\right) \ne \operatorname{decisionVisible}\left(negative\right) \land \left(\operatorname{NonAnticipating}\left(clean, true\right) \Leftrightarrow \left(\neg \operatorname{NonAnticipating}\left(decisionHidden, true\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureNecessity.DecisionVisibilityDirection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NonAnticipating is true when the selected evidence is decision-visible and false when it remains invisible.

**Definition 1.3 (Direct-contamination deletion witness).**

$$\operatorname{let} positive = \operatorname{adjudicationSignature}\left(records, emptyLedger, clean, \operatorname{emptyValid}\left(clean\right)\right), \operatorname{let} negative = \operatorname{adjudicationSignature}\left(records, emptyLedger, contaminated, \operatorname{emptyValid}\left(contaminated\right)\right), \operatorname{SameOutNA}\left(records, true\right) \land \left(\operatorname{freezeVisible}\left(positive\right) = \operatorname{freezeVisible}\left(negative\right) \land \left(\operatorname{decisionVisible}\left(positive\right) = \operatorname{decisionVisible}\left(negative\right) \land \left(\operatorname{roleProjection}\left(positive\right) = \operatorname{roleProjection}\left(negative\right) \land \left(\operatorname{directlyContaminated}\left(positive\right) \ne \operatorname{directlyContaminated}\left(negative\right) \land \left(\operatorname{NonAnticipating}\left(clean, true\right) \Leftrightarrow \left(\neg \operatorname{NonAnticipating}\left(contaminated, true\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureNecessity.DirectContaminationDirection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NonAnticipating is true with empty direct dependencies and false after adding only the selected evidence to evidenceDependencies.

**Definition 1.4 (Role-projection deletion witness).**

$$\operatorname{let} positive = \operatorname{adjudicationSignature}\left(records, judgeLedger, clean, \operatorname{judgeValid}\left(\right)\right), \operatorname{let} negative = \operatorname{adjudicationSignature}\left(records, emptyLedger, clean, \operatorname{emptyValid}\left(clean\right)\right), \operatorname{SameOutAJ}\left(records, true\right) \land \left(\operatorname{freezeVisible}\left(positive\right) = \operatorname{freezeVisible}\left(negative\right) \land \left(\operatorname{decisionVisible}\left(positive\right) = \operatorname{decisionVisible}\left(negative\right) \land \left(\operatorname{directlyContaminated}\left(positive\right) = \operatorname{directlyContaminated}\left(negative\right) \land \left(\operatorname{roleProjection}\left(positive\right) \ne \operatorname{roleProjection}\left(negative\right) \land \left(\operatorname{AdmissibleJudge}\left(judgeLedger, clean, \operatorname{judgeValid}\left(\right), true\right) \Leftrightarrow \left(\neg \operatorname{AdmissibleJudge}\left(emptyLedger, clean, \operatorname{emptyValid}\left(clean\right), true\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureNecessity.RoleProjectionDirection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

AdmissibleJudge is true with one valid in-prefix adjudicate event and false with the empty ledger; the snapshot is identical.

**Theorem 1.5 (All four surviving coordinate directions are necessary).**

$$\operatorname{FreezeVisibilityDirection}\left(\right) \land \left(\operatorname{DecisionVisibilityDirection}\left(\right) \land \left(\operatorname{DirectContaminationDirection}\left(\right) \land \operatorname{RoleProjectionDirection}\left(\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureNecessity.adjudication_signature_coordinate_necessity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first three directions select NonAnticipating, whose OP1 factorization theorem is frozen in the imported sufficiency module. The fourth selects AdmissibleJudge, whose OP1 factorization theorem is frozen there as well.

Each closed direction fixes the same nonempty Boolean record set and evidence point, states SameOut, equates all three unablated signature fields, separates the selected field, and reverses the consumer truth value.

Target laundering is not selected: its OP1 antecedent is false by the frozen target_laundering_signature_counterexample. A meaningful target-laundering necessity question must first enrich and re-establish a sufficient signature.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureNecessity.DecisionVisibilityDirection`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureNecessity.DirectContaminationDirection`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureNecessity.FreezeVisibilityDirection`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureNecessity.RoleProjectionDirection`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureNecessity.adjudication_signature_coordinate_necessity`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureSufficiency](AdjudicationSignatureSufficiency.md)
