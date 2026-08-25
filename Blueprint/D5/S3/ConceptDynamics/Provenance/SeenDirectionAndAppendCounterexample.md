# Access Direction and Early Append Witnesses

## Abstract

Direction witnesses distinguish outgoing contamination from incoming dependency closures, and an early ledger append flips admission.

**Theorem 1.1 (The direction and append boundaries are non-vacuous).**

$$roleAdmissionDirectionNonvacuity$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Provenance/SeenDirectionAndAppendCounterexample.role_admission_direction_nonvacuity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The DECT access relation reads source objects upstream into accessed objects downstream. The concrete two-element edge false -> true therefore puts true in outgoing Contam of {false}, puts false in the incoming commitment closure of {true}, and puts false in the corrected seen filtration after true is accessed.

Reversing that edge removes false from the same one-step seen prefix, so the direction claim is not a naming convention or a constant set. The aggregate theorem consumes all three named direction witnesses.

The semantic neighbor uses an old ledger containing an adjudication event and an extended ledger formed by appending a generate event with event id equal to the snapshot decision event. Its dependency touches the commitment closure: the old judge is admissible, while the extended judge is rejected by AdaptiveUseInClosure. This is the required concrete counterexample to dropping the strict post-decision condition.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Provenance/SeenDirectionAndAppendCounterexample.role_admission_direction_nonvacuity`
- Dependency: [D5/S3/ConceptDynamics/Provenance/RoleAdmissionContaminationClosure](RoleAdmissionContaminationClosure.md)
