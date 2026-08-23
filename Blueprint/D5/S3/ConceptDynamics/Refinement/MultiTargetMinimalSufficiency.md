# Minimal Sufficiency for Multiple Targets

## Abstract

The dependent joint target is the coarsest concept sufficient for every target.

**Theorem 1.1 (The joint target is minimally sufficient).**

$$\begin{gathered}\forall X, I, B_{C}: \operatorname{Type}, Y: I \to \operatorname{Type},\\{}T: \forall i\in I, X \to Y_{i},\\{}C: X \to B_{C},\\{}((\forall i\in I, \operatorname{Refines}\left(T(i), C\right)) \iff \operatorname{Refines}\left(\operatorname{jointTarget}\left(T\right), C\right)) \land\\{}(\forall i\in I, \operatorname{Refines}\left(T(i), \operatorname{jointTarget}\left(T\right)\right)) \land\\{}\forall D: \operatorname{Type}, q_{D}: X \to D, (\forall i\in I, \operatorname{Refines}\left(T(i), q_{D}\right)) \Rightarrow \operatorname{Refines}\left(\operatorname{jointTarget}\left(T\right), q_{D}\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Refinement/MultiTargetMinimalSufficiency.multi_target_minimal_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a dependent family of targets, the canonical joint target sends each state to the function listing every target value at that state.

A readout factors every component target exactly when the joint target factors through it. Evaluation at an index gives each component projection from the joint target.

For any simultaneously sufficient candidate, choosing its component factor maps and assembling them pointwise gives a joint readout factorization. This is the stated coarsest-property.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Refinement/MultiTargetMinimalSufficiency.multi_target_minimal_sufficiency`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
