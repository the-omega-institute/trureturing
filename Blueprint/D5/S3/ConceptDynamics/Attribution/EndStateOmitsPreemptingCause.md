# End States Omit Preempting Causes

## Abstract

Reversing trigger order preserves the endpoint while changing the active cause; first-trigger provenance restores recovery.

**Theorem 1.1 (An end state does not determine the preempting cause).**

$$\begin{gathered}\operatorname{IsOrderedPreemption}\left(aThenB, shooterA, shooterB\right) \land\\{}\operatorname{IsOrderedPreemption}\left(bThenA, shooterB, shooterA\right) \land\\{}\operatorname{endState}\left(aThenB\right) = \operatorname{endState}\left(bThenA\right) \land\\{}\operatorname{activeCause}\left(aThenB\right) \neq \operatorname{activeCause}\left(bThenA\right) \land\\{}\neg \exists recover: Bool \to \operatorname{Option}\left(Mechanism\right), activeCause = recover \circ endState.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/EndStateOmitsPreemptingCause.end_state_omits_preempting_cause` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In one two-step history, A triggers before B; in the reversed history, B triggers before A. Each history is an ordered preemption and reaches the same endpoint, but its first trigger, hence its active cause, is different.

Because the endpoint readout assigns the same value to histories with different active causes, no decoder from that endpoint alone can recover the active cause. The obstruction is loss of event order, not failure of either history to produce the outcome.

**Lemma 1.2 (First-trigger provenance restores active-cause recovery).**

$$\exists recover: Bool \times \operatorname{Option}\left(Mechanism\right) \to \operatorname{Option}\left(Mechanism\right), activeCause = recover \circ provenanceReadout.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/EndStateOmitsPreemptingCause.active_cause_factors_through_provenance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Refine the endpoint by recording the first trigger alongside the final outcome. The active cause is exactly this first-trigger component, so projecting the refined readout onto that component recovers the cause for every trace.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/EndStateOmitsPreemptingCause.active_cause_factors_through_provenance`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/EndStateOmitsPreemptingCause.end_state_omits_preempting_cause`
- Dependency: [D5/S3/ConceptDynamics/NormativeStructure/HistorySensitiveOutcomeReductionObstruction](../NormativeStructure/HistorySensitiveOutcomeReductionObstruction.md)
