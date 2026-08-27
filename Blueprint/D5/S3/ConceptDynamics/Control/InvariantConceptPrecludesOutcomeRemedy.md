# Invariant Concepts Preclude Outcome Remedies

## Abstract

An outcome computed from a concept preserved by every allowed action cannot be changed to a different desired value.

**Theorem 1.1 (An invariant concept precludes a different outcome remedy).**

$$\begin{gathered}\forall X, U, B, Y: \operatorname{Type},\\{}A: \operatorname{Set}\left(U\right), T: U \to \left(X \to X\right),\\{}I: X \to B, j: B \to Y, x: X,\\{}(\forall u: U, u \in A \Rightarrow I\left(T\left(u, x\right)\right) = I\left(x\right)) \Rightarrow\\{}(\forall u: U, u \in A \Rightarrow j\left(I\left(T\left(u, x\right)\right)\right) = j\left(I\left(x\right)\right)) \land\\{}(\forall yTarget: Y, yTarget \neq j\left(I\left(x\right)\right) \Rightarrow \neg(\exists u: U, u \in A \land j\left(I\left(T\left(u, x\right)\right)\right) = yTarget)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Control/InvariantConceptPrecludesOutcomeRemedy.invariant_concept_precludes_outcome_remedy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state transition is indexed by actions, and the allowed set is evaluated at the actual state. The outcome is constructed by applying j to the concept readout I.

Concept invariance transports through j, so every allowed action has the same outcome as the actual state.

Consequently, any desired outcome different from the actual outcome cannot be reached by an allowed action.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Control/InvariantConceptPrecludesOutcomeRemedy.invariant_concept_precludes_outcome_remedy`
