# Indexed Readout Monotonicity

## Abstract

Enlarging a finite index set refines its dependent joint readout and shrinks its equality kernel.

**Theorem 1.1 (Larger index sets refine joint readouts).**

$$\forall I, X: \operatorname{Type}, O: I \to \operatorname{Type}, q: \forall i: I, X \to O(i), J, K: \operatorname{Finset}\left(I\right), hJK: J \subseteq K, \operatorname{Refines}\left(q_{J}, q_{K}\right) \land \operatorname{ker}\left(q_{K}\right) \subseteq \operatorname{ker}\left(q_{J}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementFactorization/IndexedReadoutMonotonicity.indexed_readout_monotonicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a dependent readout family q_i : X -> O_i and a finite index set J, the readout q_J records exactly the coordinates in J.

When J is contained in K, coordinate restriction from the K-output to the J-output is a forgetting map. This directly witnesses that q_K refines q_J.

Equality of the K-readouts can be evaluated at every coordinate coming from J. Hence every pair identified by q_K is also identified by q_J, giving the reverse kernel inclusion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementFactorization/IndexedReadoutMonotonicity.indexed_readout_monotonicity`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
