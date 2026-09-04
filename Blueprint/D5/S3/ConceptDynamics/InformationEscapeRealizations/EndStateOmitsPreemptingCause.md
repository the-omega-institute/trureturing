# End State Omits Preempting Cause Realization

## Abstract

Endpoint and active-cause readouts realize the five-class preemption kernel.

**Theorem 1.1 (Preemption realization equivalence).**

$$\operatorname{LegacyPrimitiveRealization}\left(endStateOmitsPreemptingCauseArena, EndStateOmitsPreemptingCauseStatement, endStateOmitsPreemptingCauseRealization\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both directions encode or decode the ordered-preemption facts and preserve the object-bound factorization clause.

**Theorem 1.2 (Five kernel classes).**

$$\operatorname{card}\left(signatureClasses\right) = 5.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_partition_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Kernel evaluation groups the nine traces into the five census classes.

**Theorem 1.3 (Private trace separation).**

$$\operatorname{Not}\left(\operatorname{agrees}\left(endStateOmitsPreemptingCauseRealization, aThenB, bThenA\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_private_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiled bundle separates AB from BA through cause, admission, and anchor content.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_partition_count`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_private_pair`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_realization`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause](../InformationEscapeArenas/EndStateOmitsPreemptingCause.md)
