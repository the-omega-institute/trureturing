# Adaptive Early Stopping

## Abstract

Adaptive stopping has expectation one plus the residual-model probability, with explicit zero- and unit-error boundary cases.

**Theorem 1.1 (The residual probability is nonnegative).**

$$\forall p: \operatorname{PMF}(\operatorname{Fin}(3)), epsilon: \mathbb{R}, \operatorname{toReal}(p(M_{0})) + \operatorname{toReal}(p(M_{YX})) = epsilon \Rightarrow 0 \leq epsilon.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentDesign/AdaptiveEarlyStopping.error_probability_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both residual model masses are nonnegative because the prior is a PMF. Their prescribed sum alone forces epsilon to be nonnegative.

**Theorem 1.2 (The expected execution count is one plus epsilon).**

$$\forall p: \operatorname{PMF}(\operatorname{Fin}(3)), epsilon: \mathbb{R}, \operatorname{IsAdaptivePrior}(p, epsilon) \Rightarrow \operatorname{expectedExperimentCount}(p) = 1 + epsilon.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentDesign/AdaptiveEarlyStopping.expected_experiment_count_eq_one_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first experiment stops immediately only under M_XY. The execution count is one there and two under either residual model.

The two residual masses enter only through their sum epsilon. Hence the finite PMF-weighted sum is (1-epsilon)+2 epsilon=1+epsilon.

**Theorem 1.3 (Positive immediate-stop mass gives a strict saving).**

$$\forall p: \operatorname{PMF}(\operatorname{Fin}(3)), epsilon: \mathbb{R}, \operatorname{IsAdaptivePrior}(p, epsilon) \land epsilon < 1 \Rightarrow \operatorname{expectedExperimentCount}(p) < 2.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentDesign/AdaptiveEarlyStopping.expected_experiment_count_lt_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting the exact expectation reduces the strict comparison with two to the explicit hypothesis epsilon < 1.

**Theorem 1.4 (Zero error mass executes one experiment).**

$$\operatorname{IsAdaptivePrior}(\operatorname{pure}(M_{XY}), 0) \land \operatorname{expectedExperimentCount}(\operatorname{pure}(M_{XY})) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentDesign/AdaptiveEarlyStopping.zero_error_probability_expected_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The point mass at M_XY satisfies the adaptive prior condition with epsilon zero and makes the execution count identically one on its support.

**Theorem 1.5 (The strict epsilon hypothesis is necessary).**

$$\operatorname{IsAdaptivePrior}(\operatorname{pure}(M_{0}), 1) \land \operatorname{expectedExperimentCount}(\operatorname{pure}(M_{0})) = 2 \land \neg(\operatorname{expectedExperimentCount}(\operatorname{pure}(M_{0})) < 2).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentDesign/AdaptiveEarlyStopping.error_probability_lt_one_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At epsilon one, the point mass at M_0 satisfies the prior premise and has expected count two. The claimed strict inequality is false.

**Theorem 1.6 (Extreme residual allocations have the same expectation).**

$$\operatorname{IsAdaptivePrior}(\operatorname{pure}(M_{0}), 1) \land \operatorname{IsAdaptivePrior}(\operatorname{pure}(M_{YX}), 1) \land \operatorname{expectedExperimentCount}(\operatorname{pure}(M_{0})) = 2 \land \operatorname{expectedExperimentCount}(\operatorname{pure}(M_{YX})) = 2.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentDesign/AdaptiveEarlyStopping.extreme_remaining_allocations_same_expectation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Concentrating all residual mass on M_0 or all of it on M_YX gives expectation two in both cases, confirming that the internal split is irrelevant.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ExperimentDesign/AdaptiveEarlyStopping.error_probability_lt_one_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/ExperimentDesign/AdaptiveEarlyStopping.error_probability_nonnegative`
- Truth anchor: `D5/S3/ConceptDynamics/ExperimentDesign/AdaptiveEarlyStopping.expected_experiment_count_eq_one_add`
- Truth anchor: `D5/S3/ConceptDynamics/ExperimentDesign/AdaptiveEarlyStopping.expected_experiment_count_lt_two`
- Truth anchor: `D5/S3/ConceptDynamics/ExperimentDesign/AdaptiveEarlyStopping.extreme_remaining_allocations_same_expectation`
- Truth anchor: `D5/S3/ConceptDynamics/ExperimentDesign/AdaptiveEarlyStopping.zero_error_probability_expected_count`
