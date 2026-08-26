# Predictive Sufficiency Descent with Unique Induced Maps

## Abstract

Complete-future quotient classes carry a well-defined update and readout, with a unique pair of induced maps making both projection squares commute.

**Theorem 1.1 (Well-defined quotient dynamics and unique commuting induced maps).**

$$\forall X \in \operatorname{Type}, O \in \operatorname{Type}, update \in X \to X, readout \in X \to O,\; \left(\forall x \in X, y \in X,\; completionProjection\left(update, readout, x\right) = completionProjection\left(update, readout, y\right) \Rightarrow \left(completionProjection\left(update, readout, update\left(x\right)\right) = completionProjection\left(update, readout, update\left(y\right)\right) \land readout\left(x\right) = readout\left(y\right)\right)\right) \land \exists! induced: \operatorname{Prod}\left(\operatorname{CompletedState}\left(update, readout\right) \to \operatorname{CompletedState}\left(update, readout\right), \operatorname{CompletedState}\left(update, readout\right) \to O\right),\ \left(\forall x \in X,\; induced_{1}\left(completionProjection\left(update, readout, x\right)\right) = completionProjection\left(update, readout, update\left(x\right)\right)\right) \land \left(\forall x \in X,\; induced_{2}\left(completionProjection\left(update, readout, x\right)\right) = readout\left(x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementDescent/PredictiveSufficiencyDescent.predictive_sufficiency_descent_well_defined_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state carrier is the canonical quotient by equality of every future readout. If two representatives have the same completion projection, their updated projections and current readouts agree.

The public existential-unique clause exposes a pair consisting of an update on the completed state and a readout from it. Each component commutes with the canonical projection, and quotient surjectivity forces this pair to be unique.

The imported PredictionCompletion declarations construct the quotient, projection, quotient update, and quotient readout. The withdrawn all-computation-rule receipt is not reused as a wrapper.

Repository search found no existing theorem with both representative well-definedness and pair uniqueness at this generality; pinned Mathlib supplies Quotient.exact and Quotient.mk_surjective.

## References

- Truth anchor: `D5/S3/ObserverMemory/RefinementDescent/PredictiveSufficiencyDescent.predictive_sufficiency_descent_well_defined_unique`
- Dependency: [D5/S3/ObserverMemory/Refinement/PredictionCompletion](../Refinement/PredictionCompletion.md)
