# Nodes of a finite binary graph

## Abstract

Nodes of a finite binary graph.

**Theorem 1.1 (The exact number of distinct nodes).**

Lean statement: `D5/S0/History/Spacetime/BinaryGraphNodePoolCardinality.nodePool_card`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/BinaryGraphNodePoolCardinality.nodePool_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take an arbitrary binary word in a window of length at least three. Represent indices and bits as finite von Neumann ordinals and graph entries as Kuratowski pairs. The union of the indices, their singletons, their unordered bit pairs, and their graph entries has four times the window length minus four elements, with one additional element exactly when bit zero is one and bit two is zero. Positive-index graph entries are distinct from all earlier families. The zero-index entry either equals the singleton of ordinal one or is the unordered pair of ordinals one and two; the latter coincides with an earlier node exactly when the index-two unordered bit pair contains ordinal one. The count requires neither a terminal one nor a nonadjacency condition.

## References

- Truth anchor: `D5/S0/History/Spacetime/BinaryGraphNodePoolCardinality.nodePool_card`
- Dependency: [D5/S0/History/Spacetime/HFEncoding](HFEncoding.md)
