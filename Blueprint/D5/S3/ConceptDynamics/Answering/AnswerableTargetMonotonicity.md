# Answerable Targets Are Monotone under Refinement

## Abstract

Every target answerable through a concept remains answerable through any refinement.

**Theorem 1.1 (Answerable targets grow under concept refinement).**

$$\forall X \in Type, C \in Type, D \in Type, Y \in Type, qC \in X \to C, qD \in X \to D,\; \operatorname{Refines}\left(qC, qD\right) \Rightarrow \operatorname{AnswerableTargets}\left(qC, Y\right) \subseteq \operatorname{AnswerableTargets}\left(qD, Y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/AnswerableTargetMonotonicity.answerable_target_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A target belongs to the answerable set exactly when its canonical target readout factors through the concept. If the coarse concept itself factors through a finer concept, composing those two canonical refinement witnesses proves the required set inclusion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Answering/AnswerableTargetMonotonicity.answerable_target_monotone`
- Dependency: [D5/S3/ConceptDynamics/Refinement/RefinementTransitivity](../Refinement/RefinementTransitivity.md)
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](../Sufficiency/UniversalSufficiencyFactorization.md)
