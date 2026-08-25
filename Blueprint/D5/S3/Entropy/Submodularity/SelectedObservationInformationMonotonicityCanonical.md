# Selected Observation Information Monotonicity, Canonical Form

## Abstract

Selected canonical joint readouts carry monotone mutual information.

**Theorem 1.1 (Selected canonical readout information is monotone).**

$$\begin{gathered}\forall Sample: \operatorname{Type}, Hidden: \operatorname{Type}, Index: \operatorname{Type},\\{}Output: Index \to \operatorname{Type},\\{}(\operatorname{Fintype}(Sample) \land \operatorname{Fintype}(Hidden) \land \forall i: Index, \operatorname{Fintype}(Output(i))) \Rightarrow\\{}\forall mass: Sample \to \mathbb{R}, hidden: Sample \to Hidden,\\{}output: \forall i: Index, Sample \to Output(i),\\{}S: \operatorname{Finset}(Index), T: \operatorname{Finset}(Index),\\{}((\forall s: Sample, 0 \leq mass(s)) \land \sum_{s: Sample} mass(s) = 1) \land S \subseteq T \Rightarrow\\{}\operatorname{mutualInformation}(\operatorname{readoutTargetLaw}(mass, \operatorname{jointReadout}(j: S \mapsto output(\operatorname{val}(j))), hidden)) \leq \operatorname{mutualInformation}(\operatorname{readoutTargetLaw}(mass, \operatorname{jointReadout}(j: T \mapsto output(\operatorname{val}(j))), hidden)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/SelectedObservationInformationMonotonicityCanonical.selected_observation_information_monotone_canonical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the experiment index, hidden state, sample space, and each experiment-output alphabet be finite. A probability mass on samples and the hidden and experiment readouts construct each selected tuple through the canonical joint readout.

When S is contained in T, restricting a T-output tuple to S is deterministic postprocessing, so finite data processing gives the displayed inequality. Conditional independence is not needed for this monotonicity clause.

## References

- Truth anchor: `D5/S3/Entropy/Submodularity/SelectedObservationInformationMonotonicityCanonical.selected_observation_information_monotone_canonical`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../../ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.md)
- Dependency: [D5/S3/Entropy/Submodularity/SelectedObservationInformationMonotonicity](SelectedObservationInformationMonotonicity.md)
