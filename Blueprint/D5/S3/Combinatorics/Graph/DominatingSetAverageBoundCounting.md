# Critical Vertices and Private Neighbours

## Abstract

The critical-incidence identity and the private-neighbour estimate are Lemmas 2.1 and 2.3 of Iain Beaton and Ben Cameron, A Tight Upper Bound on the Average Order of Dominating Sets of a Graph, arXiv:2208.10475, attributed there to Beaton and Brown.

**Definition 1.1 (Critical vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.criticalVertices`

*Formalization.* `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.criticalVertices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A member of a dominating set is critical when deleting it produces a set that does not dominate the graph.

**Definition 1.2 (Private outside neighbours).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.privateNeighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.privateNeighbors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An omitted vertex is private when it has exactly one selected neighbour.

**Definition 1.3 (Externally critical vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.externallyCritical`

*Formalization.* `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.externallyCritical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A critical selected vertex is externally critical when it has a private neighbour outside the dominating set.

**Theorem 1.4 (Deletion and insertion).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.removable_pairs_eq_omitted_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.removable_pairs_eq_omitted_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Deleting a removable selected vertex and inserting an omitted vertex are mutually inverse correspondences between dominating sets differing by one vertex.

**Theorem 1.5 (Critical-incidence identity).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.critical_total_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.critical_total_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite graph of order n, the sum of the cardinalities of the critical-vertex sets plus n times the number of dominating sets equals twice the sum of the cardinalities of the dominating sets.

**Theorem 1.6 (Private-neighbour estimate).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.externallyCritical_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.externallyCritical_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite selected set, the number of externally critical vertices is at most the number of private outside neighbours. Distinct critical vertices cannot share a neighbour having only one selected neighbour.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.criticalVertices`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.critical_total_identity`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.externallyCritical`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.externallyCritical_card_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.privateNeighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.removable_pairs_eq_omitted_pairs`
- Dependency: [D5/S3/Combinatorics/Graph/DominatingSetAverage](DominatingSetAverage.md)
