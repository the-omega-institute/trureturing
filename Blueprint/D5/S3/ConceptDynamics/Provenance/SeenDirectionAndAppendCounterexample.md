# Early Append Counterexample

## Abstract

An early ledger append can flip admission when it is not strictly after the snapshot decision event.

**Theorem 1.1 (The strict post-decision premise is necessary).**

$$\operatorname{AdmissibleJudge}\left(semanticOldLedger, semanticSnapshot, semanticOldValid, false\right) \land \left(\left(\neg \operatorname{AdmissibleJudge}\left(semanticExtendedLedger, semanticSnapshot, semanticExtendedValid, false\right)\right) \land \left(\operatorname{events}\left(semanticExtendedLedger\right) = \operatorname{append}\left(\operatorname{events}\left(semanticOldLedger\right), \operatorname{singletonList}\left(semanticAdaptiveEvent\right)\right) \land \left(\operatorname{eventId}\left(semanticAdaptiveEvent\right) \le \operatorname{decisionEvent}\left(semanticSnapshot\right) \land \operatorname{Nonempty}\left(\operatorname{intersection}\left(\operatorname{dependencies}\left(semanticAdaptiveEvent\right), \operatorname{dependencyClosure}\left(semanticSnapshot\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Provenance/SeenDirectionAndAppendCounterexample.admissible_judge_early_append_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The semantic neighbor uses an old ledger containing an adjudication event and an extended ledger formed by appending a generate event with event id equal to the snapshot decision event. Its dependency touches the commitment closure: the old judge is admissible, while the extended judge is rejected by AdaptiveUseInClosure. This is the required concrete counterexample to dropping the strict post-decision condition.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Provenance/SeenDirectionAndAppendCounterexample.admissible_judge_early_append_witness`
- Dependency: [D5/S3/ConceptDynamics/Provenance/RoleAdmissionContaminationClosure](RoleAdmissionContaminationClosure.md)
