# Access Direction and Early Append Witnesses

## Abstract

Direction witnesses distinguish outgoing contamination from incoming dependency closures, and an early ledger append flips admission.

**Theorem 1.1 (The direction and append boundaries are non-vacuous).**

$$\left(true \in \operatorname{Contam}\left(directionRelation, \left\{false\right\}\right) \land \left(\neg false \in \operatorname{Contam}\left(directionRelation, \left\{true\right\}\right)\right)\right) \land \left(\left(false \in \operatorname{dependencyClosure}\left(directionSnapshot\right) \land \left(false \in \operatorname{evidenceDependencies}\left(directionSnapshot\right) \land \left(false \in \operatorname{seen}\left(\operatorname{filtration}\left(directionSnapshot\right)\right)\left(\operatorname{freezeEvent}\left(directionSnapshot\right)\right) \land \left(\neg false \in \operatorname{Contam}\left(directionRelation, \operatorname{commitmentRoots}\left(directionSnapshot\right)\right)\right)\right)\right)\right) \land \left(\left(false \in \operatorname{seen}\left(seenForward\right)\left(1\right) \land \left(\left(\neg false \in \operatorname{seen}\left(seenReverse\right)\left(1\right)\right) \land \left(\neg false \in \operatorname{seen}\left(seenForward\right)\left(0\right)\right)\right)\right) \land \left(\operatorname{AdmissibleJudge}\left(semanticOldLedger, semanticSnapshot, semanticOldValid, false\right) \land \left(\left(\neg \operatorname{AdmissibleJudge}\left(semanticExtendedLedger, semanticSnapshot, semanticExtendedValid, false\right)\right) \land \left(\operatorname{events}\left(semanticExtendedLedger\right) = \operatorname{append}\left(\operatorname{events}\left(semanticOldLedger\right), \operatorname{singletonList}\left(semanticAdaptiveEvent\right)\right) \land \left(\operatorname{eventId}\left(semanticAdaptiveEvent\right) \le \operatorname{decisionEvent}\left(semanticSnapshot\right) \land \operatorname{Nonempty}\left(\operatorname{intersection}\left(\operatorname{dependencies}\left(semanticAdaptiveEvent\right), \operatorname{dependencyClosure}\left(semanticSnapshot\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Provenance/SeenDirectionAndAppendCounterexample.role_admission_direction_nonvacuity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete two-element edge false -> true puts true in outgoing Contam of {false} and puts false in the incoming artifact dependency closure of {true}. Independently, the evidence filtration supplies a monotone seen set in which the required evidence dependency is visible at the freeze event.

Reversing that edge removes false from the same one-step seen prefix, so the direction claim is not a naming convention or a constant set. The aggregate theorem consumes all three named direction witnesses.

The semantic neighbor uses an old ledger containing an adjudication event and an extended ledger formed by appending a generate event with event id equal to the snapshot decision event. Its dependency touches the commitment closure: the old judge is admissible, while the extended judge is rejected by AdaptiveUseInClosure. This is the required concrete counterexample to dropping the strict post-decision condition.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Provenance/SeenDirectionAndAppendCounterexample.role_admission_direction_nonvacuity`
- Dependency: [D5/S3/ConceptDynamics/Provenance/RoleAdmissionContaminationClosure](RoleAdmissionContaminationClosure.md)
