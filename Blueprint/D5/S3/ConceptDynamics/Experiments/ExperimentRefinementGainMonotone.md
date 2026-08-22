# Experiment Refinement Gain Monotonicity

## Abstract

Refining an experiment only enlarges its set of repaired target defects.

**Lemma 1.1 (Target defects are antitone under refinement).**

$$\forall X, D, D', T: \operatorname{Type},\\{}q_{D}: X \to D, q_{D'}: X \to D', t: X \to T,\\{}\operatorname{Refines}\left(q_{D}, q_{D'}\right) \Rightarrow \operatorname{targetDefects}\left(q_{D'}, t\right) \subseteq \operatorname{targetDefects}\left(q_{D}, t\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiments/ExperimentRefinementGainMonotone.targetDefects_antitone_of_refines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a finer readout gives the same value on two states, then the coarser readout does as well because it factors through the finer one. The states' distinct target values are unchanged, so every defect of the finer readout was already a defect of the coarser readout.

**Lemma 1.2 (A fixed concept preserves refinement on the experiment coordinate).**

$$\forall X, C, E, E': \operatorname{Type},\\{}q_{C}: X \to C, q_{E}: X \to E, q_{E'}: X \to E',\\{}\operatorname{Refines}\left(q_{E}, q_{E'}\right) \Rightarrow \operatorname{Refines}\left(\operatorname{conceptJoin}\left(q_{C}, q_{E}\right), \operatorname{conceptJoin}\left(q_{C}, q_{E'}\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiments/ExperimentRefinementGainMonotone.conceptJoin_refines_of_right_refines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When one experiment readout factors through another, adjoining the same concept readout to both preserves that factorization. The induced factor map leaves the concept coordinate fixed and applies the experiment factor map to the second coordinate.

**Theorem 1.3 (Experiment refinement can only enlarge gain).**

$$\forall X, C, E, E', T: \operatorname{Type},\\{}q_{C}: X \to C, q_{E}: X \to E, q_{E'}: X \to E', t: X \to T,\\{}\\{}\operatorname{Refines}\left(q_{E}, q_{E'}\right) \Rightarrow \operatorname{experimentGain}\left(q_{C}, q_{E}, t\right) \subseteq \operatorname{experimentGain}\left(q_{C}, q_{E'}, t\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiments/ExperimentRefinementGainMonotone.experiment_refinement_gain_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Gain consists of target defects of the fixed concept that disappear after the experiment is joined to it. Refining the experiment shrinks the joined readout's remaining target-defect set.

Subtracting that smaller remaining-defect set from the same base set can only add repaired pairs. Thus every defect repaired by the coarser experiment is also repaired by the finer experiment.

**Theorem 1.4 (A refined experiment does not reintroduce a repaired defect).**

$$\forall X, C, E, E', T: \operatorname{Type},\\{}q_{C}: X \to C, q_{E}: X \to E, q_{E'}: X \to E', t: X \to T,\\{}p: X \times X,\\{}\operatorname{Refines}\left(q_{E}, q_{E'}\right) \land p \in \operatorname{targetDefects}\left(q_{C}, t\right) \land \neg {p \in \operatorname{targetDefects}\left(\operatorname{conceptJoin}\left(q_{C}, q_{E}\right), t\right)} \Rightarrow\\{}\neg {p \in \operatorname{targetDefects}\left(\operatorname{conceptJoin}\left(q_{C}, q_{E'}\right), t\right)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiments/ExperimentRefinementGainMonotone.refined_experiment_does_not_reintroduce_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a pair that is a target defect of the fixed concept but is separated after adjoining the coarser experiment. Gain monotonicity keeps that pair in the refined experiment's gain, so the finer joined readout cannot identify the pair again.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiments/ExperimentRefinementGainMonotone.conceptJoin_refines_of_right_refines`
- Truth anchor: `D5/S3/ConceptDynamics/Experiments/ExperimentRefinementGainMonotone.experiment_refinement_gain_monotone`
- Truth anchor: `D5/S3/ConceptDynamics/Experiments/ExperimentRefinementGainMonotone.refined_experiment_does_not_reintroduce_defect`
- Truth anchor: `D5/S3/ConceptDynamics/Experiments/ExperimentRefinementGainMonotone.targetDefects_antitone_of_refines`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
