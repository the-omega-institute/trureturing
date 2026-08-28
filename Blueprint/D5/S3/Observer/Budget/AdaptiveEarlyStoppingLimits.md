# Adaptive Early Stopping Limits

## Abstract

Adaptive early stopping lowers a concrete expected count while preserving the adaptive worst-case information bound and the fixed answer alphabet.

**Theorem 1.1 (Early stopping retains the adaptive worst-case lower bound).**

$$\operatorname{clog}(B, \operatorname{card}(X)) \leq \operatorname{adaptiveIdentificationDepth}(X, q).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/AdaptiveEarlyStoppingLimits.adaptive_worst_case_depth_information_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported adaptive protocol already permits a leaf under any remaining budget. Its logarithmic lower bound therefore applies directly for positive branching, while the totalized base-zero logarithm is zero.

**Theorem 1.2 (Full transcript spaces attain the worst-case lower bound).**

$$1 < B \implies \operatorname{adaptiveIdentificationDepth}(\operatorname{TranscriptSpace}(B, h), \operatorname{coordinateReadout}(B, h)) = h.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/AdaptiveEarlyStoppingLimits.adaptive_worst_case_depth_lower_bound_is_tight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For more than one possible answer, coordinate questions identify all B-valued transcripts of length h. The imported cardinality equality and the lower bound force the least adaptive depth to equal h.

**Lemma 1.3 (Nonunary branching is necessary for positive-depth tightness).**

$$\operatorname{adaptiveIdentificationDepth}(\operatorname{TranscriptSpace}(1, 1), \operatorname{coordinateReadout}(1, 1)) = 0 \land \operatorname{adaptiveIdentificationDepth}(\operatorname{TranscriptSpace}(1, 1), \operatorname{coordinateReadout}(1, 1)) \neq 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/AdaptiveEarlyStoppingLimits.branching_gt_one_is_necessary_for_positive_depth_tightness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At B=1 and nominal depth one, the transcript state space is a singleton. A root leaf identifies it at depth zero, so equality with depth one is false.

**Theorem 1.4 (One experiment has at most B attained answers).**

$$\operatorname{card}(\operatorname{singleExperimentOutputs}(q)) \leq B.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/AdaptiveEarlyStoppingLimits.single_experiment_output_count_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every adaptive query returns a value in Fin B by definition. The attained image is a subset of that fixed alphabet, so its cardinality is at most B independently of how later questions are selected.

**Lemma 1.5 (The single-experiment output bound is attained).**

$$\operatorname{card}(\operatorname{singleExperimentOutputs}(\operatorname{identityOn}(\operatorname{Fin}(B)))) = B.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/AdaptiveEarlyStoppingLimits.identity_experiment_attains_output_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity experiment on Fin B realizes every output. This also covers B=0, where both the state space and attained output set are empty.

**Lemma 1.6 (Empty and unary experiments have the expected output counts).**

$$\operatorname{card}(\operatorname{singleExperimentOutputs}(emptyToFinZero)) = 0 \land \operatorname{card}(\operatorname{singleExperimentOutputs}(unitToFinOne)) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/AdaptiveEarlyStoppingLimits.single_experiment_degenerate_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An experiment on Empty with an empty alphabet attains no answer. A constant unary experiment on Unit attains exactly its sole answer.

**Lemma 1.7 (Zero depth and constant-readout boundaries are explicit).**

$$\operatorname{ExactAtDepth}(qEmpty, 0) \land \operatorname{ExactAtDepth}(qUnit, 0) \land \operatorname{clog}(1, 1) = 0 \land \forall h, \neg\operatorname{ExactAtDepth}(\operatorname{constantZero}(2), h).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/AdaptiveEarlyStoppingLimits.protocol_degenerate_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Imported named audits identify Empty and Unit at depth zero and rule out identifying Bool with a constant binary readout. Unary clog is zero.

**Lemma 1.8 (Doing every experiment removes the average saving).**

$$\operatorname{expectedExperimentCount}(\operatorname{pure}(M0)) = 2.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/AdaptiveEarlyStoppingLimits.all_experiments_required_has_no_average_saving` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported three-model example has a point mass on a branch that cannot stop after the first question. Its adaptive count is exactly two, matching the static count.

## References

- Truth anchor: `D5/S3/Observer/Budget/AdaptiveEarlyStoppingLimits.adaptive_worst_case_depth_information_lower_bound`
- Truth anchor: `D5/S3/Observer/Budget/AdaptiveEarlyStoppingLimits.adaptive_worst_case_depth_lower_bound_is_tight`
- Truth anchor: `D5/S3/Observer/Budget/AdaptiveEarlyStoppingLimits.all_experiments_required_has_no_average_saving`
- Truth anchor: `D5/S3/Observer/Budget/AdaptiveEarlyStoppingLimits.branching_gt_one_is_necessary_for_positive_depth_tightness`
- Truth anchor: `D5/S3/Observer/Budget/AdaptiveEarlyStoppingLimits.identity_experiment_attains_output_bound`
- Truth anchor: `D5/S3/Observer/Budget/AdaptiveEarlyStoppingLimits.protocol_degenerate_audit`
- Truth anchor: `D5/S3/Observer/Budget/AdaptiveEarlyStoppingLimits.single_experiment_degenerate_audit`
- Truth anchor: `D5/S3/Observer/Budget/AdaptiveEarlyStoppingLimits.single_experiment_output_count_le`
- Dependency: [D5/S3/ConceptDynamics/ExperimentDesign/AdaptiveEarlyStopping](../../ConceptDynamics/ExperimentDesign/AdaptiveEarlyStopping.md)
- Dependency: [D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound](WorstCaseDepthInformationLowerBound.md)
