# Selected Observation Information Monotonicity

## Abstract

Selected finite experiments carry monotone information about a hidden state.

**Theorem 1.1 (Selected observation information is monotone).**

$$\left(\operatorname{ProbabilityLaw}\left(p\right) \land S \subseteq T\right) \Rightarrow \operatorname{selectedObservationInformation}\left(p, X, Y, S\right) \le \operatorname{selectedObservationInformation}\left(p, X, Y, T\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/SelectedObservationInformationMonotonicity.selected_observation_information_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the experiment index, hidden state, sample space, and each experiment-output alphabet be finite. A probability mass on samples and the hidden and experiment readouts construct the selected output tuple and its joint law with the hidden state.

When S is contained in T, restriction of a T-output tuple to S is deterministic postprocessing. Finite data processing therefore gives F(S) at most F(T), where F is the mutual information of the constructed selected-output joint law. This monotonicity holds without the source section's stronger conditional-independence assumption.

## References

- Truth anchor: `D5/S3/Entropy/Submodularity/SelectedObservationInformationMonotonicity.selected_observation_information_monotone`
- Dependency: [D5/S3/ConceptDynamics/Communication/TranslationLossMonotonicity](../../ConceptDynamics/Communication/TranslationLossMonotonicity.md)
