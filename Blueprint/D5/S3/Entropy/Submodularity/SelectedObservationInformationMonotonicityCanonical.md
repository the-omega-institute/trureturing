# Selected Observation Information Monotonicity, Canonical Form

## Abstract

Selected canonical joint readouts carry monotone mutual information.

**Theorem 1.1 (Selected canonical readout information is monotone).**

$$\left(\operatorname{ProbabilityLaw}(p) \land S \subseteq T\right) \Rightarrow \operatorname{mutualInformation}(\operatorname{readoutTargetLaw}(p, \operatorname{jointReadout}(Y \mid S), X)) \le \operatorname{mutualInformation}(\operatorname{readoutTargetLaw}(p, \operatorname{jointReadout}(Y \mid T), X))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/SelectedObservationInformationMonotonicityCanonical.selected_observation_information_monotone_canonical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the experiment index, hidden state, sample space, and each experiment-output alphabet be finite. A probability mass on samples and the hidden and experiment readouts construct each selected tuple through the canonical joint readout.

When S is contained in T, restricting a T-output tuple to S is deterministic postprocessing, so finite data processing gives the displayed inequality. Conditional independence is not needed for this monotonicity clause.

## References

- Truth anchor: `D5/S3/Entropy/Submodularity/SelectedObservationInformationMonotonicityCanonical.selected_observation_information_monotone_canonical`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../../ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.md)
- Dependency: [D5/S3/Entropy/Submodularity/SelectedObservationInformationMonotonicity](SelectedObservationInformationMonotonicity.md)
