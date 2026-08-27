# Positive First-Experiment Identification

## Abstract

A positive first experiment identifies the forward causal model.

**Theorem 1.1 (A positive first result identifies the model).**

$$\forall m: \operatorname{Fin}\left(3\right), E_{X}(m) = true \Rightarrow m = M_{XY}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentDesign/PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first experiment is the canonical Boolean readout on the three-model carrier. By construction it is positive exactly on the model in which changing X changes the law of Y.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ExperimentDesign/PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model`
- Dependency: [D5/S3/ConceptDynamics/ExperimentDesign/AdaptiveEarlyStopping](AdaptiveEarlyStopping.md)
