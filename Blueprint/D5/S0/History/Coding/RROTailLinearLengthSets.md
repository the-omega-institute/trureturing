# RRO Tail Linear-Length Sets

## Abstract

The Boolean cube admits linear-length disjoint terminal fibres with edge contacts.

**Theorem 1.1 (Linear-length fibres and distance-two contacts).**

Lean statement: `D5/S0/History/Coding/RROTailLinearLengthSets.proposition_36_1`

*Proof.* Machine-checked in Lean as `D5/S0/History/Coding/RROTailLinearLengthSets.proposition_36_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive k, take the Boolean k-cube. Its edge set has k·2^(k−1) elements, while prefixes of length k−1+ceil(log₂ k) have at least that many values. An injective prefix assignment therefore labels every edge.

At a vertex, attach to each incident edge the assigned prefix and a final bit determined by a fixed total ordering of the two endpoints. The resulting fibre has exactly k words; distinct fibres are disjoint because equal prefixes identify an edge and the two endpoint bits are opposite.

Each cube edge contributes one word to each endpoint fibre with a common prefix and opposite final bits, which is the stated distance-two contact. The word length is (k−1+ceil(log₂ k))+1 = k+ceil(log₂ k).

## References

- Truth anchor: `D5/S0/History/Coding/RROTailLinearLengthSets.proposition_36_1`
- Dependency: [D5/S3/Combinatorics/Graph/Hypercube](../../../S3/Combinatorics/Graph/Hypercube.md)
