# Target-Relevant Omission

## Abstract

A target-relevant omission is exactly a collapsed message distinction that matters to the target.

**Theorem 1.1 (Target-relevant omission has a collapsed distinction witness).**

$$\forall X \in Type, S \in Type, M \in Type, Target \in Type, sender \in X \to S, encoder \in S \to M, target \in X \to Target,\; \left(\operatorname{Nonempty}\left(X\right) \land \operatorname{Refines}\left(target, sender\right)\right) \Rightarrow \left(\operatorname{TargetRelevantOmission}\left(sender, encoder, target\right) \Leftrightarrow \left(\exists x \in X, y \in X,\; \operatorname{messageConcept}\left(sender, encoder, x\right) = \operatorname{messageConcept}\left(sender, encoder, y\right) \land \left(target\left(x\right) \ne target\left(y\right) \land sender\left(x\right) \ne sender\left(y\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/TargetRelevantOmission.omission_iff_witness_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty state space, assume the sender determines the target. The encoding has a target-relevant omission exactly when two states produce the same message while having different target values and different sender coordinates.

In the forward direction, failure to recover the target from the message yields a message fiber on which the target varies. Since the target factors through the sender, that pair must also differ at the sender. Conversely, such a pair rules out every recovery map from messages to target values.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/TargetRelevantOmission.omission_iff_witness_exists`
- Dependency: [D5/S3/ConceptDynamics/Coding/LosslessEncodingCriterion](LosslessEncodingCriterion.md)
