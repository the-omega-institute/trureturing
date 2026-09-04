# End State Omits Preempting Cause Realization

## Abstract

Endpoint and active-cause readouts realize the five-class preemption kernel.

**Definition 1.1 (Concrete preemption realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The realization supplies endpoint, active-cause, ordered-preemption, and named-anchor data.

**Theorem 1.2 (Preemption realization equivalence).**

$$\operatorname{IsOrderedPreemption}(aThenB, shooterA, shooterB) \land \operatorname{IsOrderedPreemption}(bThenA, shooterB, shooterA) \land \operatorname{endState}(aThenB) = \operatorname{endState}(bThenA) \land \operatorname{activeCause}(aThenB) \neq \operatorname{activeCause}(bThenA) \land \neg {\exists recover: Bool \to \operatorname{Option}(Mechanism), activeCause = recover \circ endState} \iff endStateOmitsPreemptingCauseArena.Law endStateOmitsPreemptingCauseRealization.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both directions encode or decode every clause of the frozen preemption statement.

**Theorem 1.3 (Five kernel classes).**

$$(Finset.univ.image(\lambda trace: PreemptionTrace, (\operatorname{endState}(trace), \operatorname{activeCause}(trace), \operatorname{decide}(\operatorname{IsOrderedPreemption}(trace, shooterA, shooterB)), \operatorname{decide}(\operatorname{IsOrderedPreemption}(trace, shooterB, shooterA)), \operatorname{decide}(trace = aThenB), \operatorname{decide}(trace = bThenA)))).card = 5.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_partition_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete six-component image of all preemption traces has five elements.

**Theorem 1.4 (Private trace separation).**

$$\neg {endStateOmitsPreemptingCauseRealization.toPrimitiveBundle.agrees aThenB bThenA}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_private_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiled primitive bundle separates the two named traces.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_partition_count`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_private_pair`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_realization`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause](../InformationEscapeArenas/EndStateOmitsPreemptingCause.md)
