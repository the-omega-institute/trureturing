# Indexed Common-Source Upper Bound

## Abstract

An indexed family of messages cannot jointly distinguish more than its common source readout.

**Theorem 1.1 (The joint message readout remains below its common source).**

$$\begin{aligned}\forall I, X, B: \operatorname{Type}, M: I \to \operatorname{Type},\\m: \forall i: I, X \to M_{i}, s: X \to B,\\(\forall i: I, \operatorname{Refines}\left(m\left(i\right), s\right)) \Rightarrow \operatorname{Refines}\left(\operatorname{jointReadout}\left(m\right), s\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Communication/IndexedCommonSourceUpperBound.indexed_common_source_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each component premise supplies a factor from the common source value to that message value. The proof selects those factors and bundles their outputs into the canonical dependent joint readout.

Evaluating the assembled factor at a state reduces componentwise to the given message factorization, so the entire message family remains a postprocessing of the same source.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Communication/IndexedCommonSourceUpperBound.indexed_common_source_upper_bound`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
