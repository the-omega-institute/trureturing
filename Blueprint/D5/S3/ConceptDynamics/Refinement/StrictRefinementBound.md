# Finite Strict Refinement Bound

## Abstract

A finite state space bounds the number of strict concept refinements.

**Theorem 1.1 (Strict refinements terminate within the cardinality deficit).**

$$\forall X, B: \operatorname{Type}, [\operatorname{Finite} X],\ s\in \mathbb{N}, C: \operatorname{Fin}(s+1) \to (X \to B),\\(\forall i: \operatorname{Fin}(s), \operatorname{StrictlyRefines}\left(C_{i}, C_{i+1}\right)) \Rightarrow\\s \leq \lvert X\rvert - \lvert \operatorname{range}(C_{0})\rvert.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Refinement/StrictRefinementBound.strict_refinement_steps_le_card_sub_initial_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A concept readout identifies two states when their coordinates agree. A strict refinement preserves every distinction made by the coarse readout and splits at least one of its equivalence classes.

For finite X, each strict step therefore increases the cardinality of the readout image by at least one. The final image injects into X through representatives, so its cardinality is at most the cardinality of X.

Combining growth over all steps with the final image bound gives exactly the number of states minus the initial image size. A constant Boolean readout refined by the identity supplies a machine-checked nonempty model.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Refinement/StrictRefinementBound.strict_refinement_steps_le_card_sub_initial_image`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
