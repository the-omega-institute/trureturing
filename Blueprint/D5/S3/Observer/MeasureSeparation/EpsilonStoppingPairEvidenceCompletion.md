# Epsilon Stopping and Pair-Evidence Completion

## Abstract

Epsilon stopping and pair evidence yield a common classifier under a named dichotomy.

**Definition 1.1 (Posterior MAP error).**

$$\operatorname{posteriorError}\left(pi\right) = 1 - \operatorname{supPosteriorMass}\left(pi\right)$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.posteriorError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The error is one minus the supremum posterior mass. On a finite nonempty state type, this supremum is the maximum in Definition 250.1.

**Definition 1.2 (Epsilon-completion stopping time).**

$$\operatorname{epsilonStoppingTime}\left(epsilon, pi\right) = \operatorname{firstOrInfinity}\left(\operatorname{errorAtMost}\left(pi, epsilon\right)\right)$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.epsilonStoppingTime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first threshold-hitting natural time is returned. Infinity explicitly records an empty threshold set.

**Definition 1.3 (Abstract measure affinity).**

$$\operatorname{MeasureAffinity}\left(Omega\right) = \operatorname{binaryMap}\left(\operatorname{Measure}\left(Omega\right), ENNReal\right)$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.MeasureAffinity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the named abstract interface used because pinned Mathlib has no measure-level Hellinger affinity. Hellinger affinity is an intended instance, not constructed here.

**Definition 1.4 (Open-loop pair evidence).**

$$\operatorname{openLoopPairEvidence}\left(x, y\right) = \operatorname{infiniteSum}\left(t, 2 \cdot \left(1 - \operatorname{rho}\left(t, x, y\right)\right)\right)$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.openLoopPairEvidence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The experiment sequence is fixed, and evidence is summed with the repository convention H squared equals twice one minus affinity.

**Definition 1.5 (Selected local laws are equivalent).**

$$\operatorname{allSelectedDistinctLocalLawsEquivalent}\left(K, i\right)$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.OpenLoopLocallyEquivalent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At every selected coordinate, the laws for each distinct state pair are mutually absolutely continuous.

**Definition 1.6 (Named evidence-to-singularity bridge).**

$$\left(\operatorname{OpenLoopLocallyEquivalent}\left(K, i\right) \land \operatorname{allPairEvidenceInfinite}\left(rho, K, i\right)\right) \Rightarrow \operatorname{PairwiseMutuallySingular}\left(transcriptLaw\right)$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.OpenLoopEvidenceDichotomy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This packages the missing Kakutani implication as an explicit premise. It does not claim a product-measure dichotomy from pinned Mathlib.

**Definition 1.7 (Common zero-error decision regions).**

$$\operatorname{measurableDisjointConullDecisionRegions}\left(transcriptLaw\right)$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.HasCommonZeroErrorClassifier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A classifier is represented by measurable pairwise disjoint regions whose complements are null under their corresponding transcript laws.

**Definition 1.8 (Extended negative log affinity).**

$$\operatorname{negativeLogAffinity}\left(rho\right) = \operatorname{toENNReal}\left((-\log rho)\right)$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.negativeLogAffinity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The extended nonnegative value is infinite at zero. Values above one truncate to zero; intended normalized affinities lie in the unit interval.

**Definition 1.9 (History-conditional affinity).**

$$\operatorname{conditionalAffinity}\left(x, y, t, h\right) = \operatorname{rho}\left(\operatorname{K}\left(\operatorname{policy}\left(t, h\right), x\right), \operatorname{K}\left(\operatorname{policy}\left(t, h\right), y\right)\right)$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.conditionalAffinity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At time t, the common history is fed to the policy and the selected local laws are compared by the abstract affinity.

**Definition 1.10 (Predictable evidence process).**

$$\operatorname{predictableEvidenceProcess}\left(n, x, y\right) = \operatorname{finiteSumBefore}\left(n, \operatorname{negativeLogConditionalAffinity}\left(x, y\right)\right)$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.predictableEvidenceProcess` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evidence before n is the finite sum of negative log conditional affinities along the common-history process.

**Theorem 1.11 (Infinite stopping exactly means no threshold hit).**

$$\operatorname{epsilonStoppingTime}\left(epsilon, pi\right) = \infty \Leftrightarrow \operatorname{noTimeHasErrorAtMost}\left(pi, epsilon\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.epsilon_stopping_time_eq_top_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This records the empty threshold-set behavior explicitly.

**Theorem 1.12 (An initial threshold hit stops at zero).**

$$\operatorname{errorAtZeroAtMost}\left(pi, epsilon\right) \Rightarrow \operatorname{epsilonStoppingTime}\left(epsilon, pi\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.epsilon_stopping_time_eq_zero_of_initial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Natural-number minimality makes time zero the first hit.

**Theorem 1.13 (Threshold one stops immediately).**

$$\operatorname{epsilonStoppingTime}\left(1, pi\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.epsilon_one_stops_immediately` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Posterior error is always at most one.

**Theorem 1.14 (Singleton posterior error is zero).**

$$\operatorname{posteriorError}\left(\operatorname{PMF}\left(Unit\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.posterior_error_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The only state has posterior mass one.

**Theorem 1.15 (A singleton state space stops immediately).**

$$\operatorname{epsilonStoppingTime}\left(epsilon, \operatorname{PMFProcess}\left(Unit\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.singleton_state_stops_immediately` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero posterior error meets every extended nonnegative threshold at time zero.

**Theorem 1.16 (The empty state type has no posterior).**

$$\operatorname{IsEmpty}\left(\operatorname{PMF}\left(\emptyset\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.empty_state_has_no_posterior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A probability mass function cannot normalize on an empty type.

**Theorem 1.17 (A zero threshold may never be reached).**

$$\operatorname{epsilonStoppingTime}\left(0, \operatorname{constantFairPosterior}\left(Bool\right)\right) = \infty$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.zero_threshold_may_never_stop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant fair Boolean posterior has strictly positive error forever.

**Theorem 1.18 (Singleton pair evidence is vacuous).**

$$\operatorname{allDistinctPairEvidenceInfiniteVacuously}\left(Unit\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.singleton_pair_evidence_condition_vacuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are no distinct state pairs on Unit.

**Theorem 1.19 (Finite singular laws admit one common classifier).**

$$\operatorname{FinitePairwiseMutuallySingular}\left(transcriptLaw\right) \Rightarrow \operatorname{HasCommonZeroErrorClassifier}\left(transcriptLaw\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.finite_pairwise_singular_common_zero_error_classifier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Canonical measurable refinement turns finite pairwise singular separators into pairwise disjoint conull decision regions.

**Theorem 1.20 (Open-loop completion under the named dichotomy).**

$$\left(\operatorname{OpenLoopLocallyEquivalent}\left(K, i\right) \land \left(\operatorname{allPairEvidenceInfinite}\left(rho, K, i\right) \land \operatorname{OpenLoopEvidenceDichotomy}\left(rho, K, i\right)\right)\right) \Rightarrow \left(\operatorname{PairwiseMutuallySingular}\left(transcriptLaw\right) \land \operatorname{HasCommonZeroErrorClassifier}\left(transcriptLaw\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.open_loop_finite_state_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Local equivalence and divergent pair evidence feed the explicit dichotomy. Finite pairwise singularity then yields a common zero-error classifier.

**Theorem 1.21 (The abstract setting needs a dichotomy premise).**

$$\operatorname{existsZeroAffinityIdenticalDiracCounterexample}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.evidence_dichotomy_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Constant zero affinity makes all evidence infinite while identical Dirac transcript laws remain nonsingular.

**Theorem 1.22 (Zero affinity has infinite evidence).**

$$\operatorname{negativeLogAffinity}\left(0\right) = \infty$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.negative_log_affinity_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The extended logarithm sends zero affinity to infinite negative-log evidence.

**Theorem 1.23 (Predictable evidence starts at zero).**

$$\operatorname{predictableEvidenceProcess}\left(0, x, y\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.predictable_evidence_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite sum before time zero has no terms.

## References

- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.HasCommonZeroErrorClassifier`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.MeasureAffinity`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.OpenLoopEvidenceDichotomy`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.OpenLoopLocallyEquivalent`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.conditionalAffinity`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.empty_state_has_no_posterior`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.epsilonStoppingTime`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.epsilon_one_stops_immediately`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.epsilon_stopping_time_eq_top_iff`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.epsilon_stopping_time_eq_zero_of_initial`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.evidence_dichotomy_is_necessary`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.finite_pairwise_singular_common_zero_error_classifier`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.negativeLogAffinity`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.negative_log_affinity_zero`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.openLoopPairEvidence`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.open_loop_finite_state_completion`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.posteriorError`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.posterior_error_singleton`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.predictableEvidenceProcess`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.predictable_evidence_zero`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.singleton_pair_evidence_condition_vacuous`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.singleton_state_stops_immediately`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.zero_threshold_may_never_stop`
