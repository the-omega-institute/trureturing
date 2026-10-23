# Stopping at the fixed original target

## Abstract

Stopping at the fixed original target

**Theorem 1.1 (Every observable finite-event class choice has positive error).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping.local_choice_positive_error`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping.local_choice_positive_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every measurable independent seed probability, finite radius r, positive actual product-law event E and arbitrary returned-label map C, assume every E intersect {C=a} belongs to the completed enlarged past field at r. Then E intersect {C differs from fixed Q0} has strictly positive actual product-law mass. The choice needs to be observable only on E. The finite label partition supplies a positive cell, where local_positive_error applies. finite_return_error consumes this helper; the completed-field and common-law conditions are retained.

**Theorem 1.2 (The same fixed-target past fields increase).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping.past_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping.past_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural r, pastField(r) is a subfield of pastField(r+1), using the chronological projection deleting the oldest observed bit. FixedTargetRecovery uses this exact original supplier to form one nested filtration.

The process is the original twelve-state bilateral hidden/output process with law J, and target is the phase and residue modulo three of H(0). An arbitrary measurable seed space U carries a probability nu independent of the entire process. The single extended law is J times nu. No change of hidden law or target occurs when the past radius increases.

**Definition 1.3 (Completed nested past information).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping.pastFiltration`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping.pastFiltration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every seed measure nu, pastFiltration(nu) is a natural-number-indexed Filtration on the null-measurable completion of the product process and seed space. At radius r its measurable events are exactly those equal almost everywhere under J times nu to an event in enlarged(pastField(r)). Thus the whole seed is available at every radius, and completion includes the null events of the whole ambient law. A measurable representative can be used even when the completed event itself is not measurable in the raw product sigma algebra.

The radius-r word is the suffix of length r of the radius-r+1 word: deleting the oldest symbol preserves coordinates -r through -1. The sigma fields therefore increase pathwise by an explicit factor map, with target fixed at zero. Product enlargement and completion preserve inclusion. Every completed field lies in the ambient null-measurable completion because its raw representative is ambient measurable. Stationarity is not used to transport a filtration or a stopping rule.

**Theorem 1.4 (The posterior identity in the completed enlarged field).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping.actual_completed_posterior`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping.actual_completed_posterior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every measurable independent whole-process seed space U with probability nu, every finite natural radius r including zero, and each actual class a, the original J-conditional expectation of the target=a indicator given pastField(r), pulled back by the process projection, equals almost everywhere under J times nu the conditional expectation of that same indicator under the completion of J times nu given pastFiltration(nu,r). The latter field is the completed enlarged field itself, not the raw product field.

To prove the completion step, take a raw measurable representative of every completed event. The original and completed measures agree on all sets and have the same almost-everywhere filter. Trimming the completed measure to the raw ambient field recovers the raw measure; the integrals of the raw measurable indicator and its raw conditional expectation therefore agree with their completed-measure integrals. Almost-everywhere equality of the events extends the conditional-expectation integral identity to every completed event. Conditional-expectation uniqueness, followed by the existing product bridge, gives the stated identity. The fixed target remains H(0)'s phase and residue at every radius.

**Theorem 1.5 (Positive observable returns have positive local error).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping.local_positive_error`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping.local_positive_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every measurable seed space U, probability nu on U, finite natural radius r including zero, actual class label a, and event E measurable in pastFiltration(nu,r), positive product-law mass of E implies positive product-law mass of E intersected with the event target not equal to a. This is a strict positivity assertion for each event and radius; no positive lower bound uniform in the radius is asserted.

Choose a raw measurable representative B of E. Its information is included in radius r+1. The independent-seed posterior theorem puts the conditional probability of every fixed class strictly below one almost everywhere at this positive radius. If error on B had zero mass, the target indicator would equal one almost everywhere on B. The conditional-expectation integral identity would then make the integral over B of one minus that posterior zero. This integrable function is strictly positive almost everywhere on B, so its integral is positive when B has positive mass, a contradiction. Almost-everywhere equivalence transfers both event and error masses back to E. The use of radius r+1 also treats r=0 without assuming a nonempty radius-zero observation.

**Theorem 1.6 (Every positive finite-return probability entails positive error).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping.finite_return_error`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping.finite_return_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every measurable seed space U and probability nu, let tau map the product process and seed space to the natural numbers with infinity adjoined, and let A map that space to the six actual labels. Suppose that for each finite r and each label a, the event tau=r and A=a is measurable in pastFiltration(nu,r). Then tau is a genuine IsStoppingTime for that completed filtration. Moreover, if the product-law probability of tau being finite is positive, the product-law probability that tau is finite and A differs from the fixed target is positive. There is no assumption that tau is finite almost surely, and no restriction is imposed on A on the infinite-return event.

For each finite r, the return event is the finite union of its observable returned-label cells, which proves the stopping-time assertion. The event of any finite return is the countable union of all radius and label cells. Positive total mass forces a positive cell. The local positive-error theorem applies to that cell, whose error event is contained in the event of a finite incorrect return. Hence zero error on finite returns forces zero probability of a finite return. This does not identify an observable certificate for samplewise eventual correctness, establish an error floor, or assert physical access to an observation archive.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping.actual_completed_posterior`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping.finite_return_error`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping.local_choice_positive_error`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping.local_positive_error`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping.pastFiltration`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping.past_succ`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/IndependentSeedPosterior](IndependentSeedPosterior.md)
