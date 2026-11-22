# Ordered partitions and face order

## Abstract

Ordered partitions and face order.

**Theorem 1.1 (Rank).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.rank_toCuts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.rank_toCuts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

An ordered partition with b blocks has exactly b minus one proper cumulative cuts. Its face rank is n minus b.

**Definition 1.2 (The face dictionary).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.orderedPartitionsEquiv`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.orderedPartitionsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

An ordered partition is a surjective map from the labels to a nonempty finite linear order of blocks. Taking all proper cumulative cuts gives a cut chain. Conversely, a chain gives an ordered partition whose blocks are the successive differences, including the complement of the largest cut. These maps are inverse when the label set is nonempty.

**Theorem 1.3 (Adjacent block merges).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.mergesAdjacent_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.mergesAdjacent_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

One partition is obtained from another by merging adjacent blocks exactly when its family of cumulative cuts is contained in the other's family. The merging map on block labels is monotone and surjective.

**Definition 1.4 (Singleton-block partitions).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.permutationAtomsEquiv`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.permutationAtomsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

Permutation flags recover each entry by the difference between successive prefixes, including the final label. Consequently permutations correspond bijectively to atoms.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.mergesAdjacent_iff`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.orderedPartitionsEquiv`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.permutationAtomsEquiv`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.rank_toCuts`
- Dependency: [D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags](FaceFlags.md)
