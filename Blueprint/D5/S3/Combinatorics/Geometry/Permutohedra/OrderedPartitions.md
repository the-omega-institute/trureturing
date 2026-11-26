# Ordered partitions and face order

## Abstract

Ordered partitions and face order.

**Definition 1.1 (Ordered partitions).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.OrderedPartition`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.OrderedPartition` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

An ordered partition of Fin n specifies a natural number of separators and a surjection from the labels onto the ordered block indices, whose count is one plus the number of separators.

**Definition 1.2 (A cumulative cut).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.cut`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.cut` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

At a zero-based separator index i, take all labels whose block index is at most i.

**Definition 1.3 (The chain of cumulative cuts).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.toCuts`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.toCuts` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

Take the cumulative cut at every separator. Surjectivity makes each cut proper and nonempty, and the cuts are nested in separator order.

**Theorem 1.4 (Rank).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.rank_toCuts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.rank_toCuts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

An ordered partition with b blocks has exactly b minus one proper cumulative cuts. Its face rank is n minus b.

**Definition 1.5 (The partition of a chain).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.toPartition`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.toPartition` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

On a nonempty label set, order the cuts by increasing size. Use the cuts as separators, and send each label to the block indexed by the number of cuts that omit it. The successive differences and the complement of the largest cut give the nonempty blocks. An empty chain gives a single block.

**Definition 1.6 (The face dictionary).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.orderedPartitionsEquiv`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.orderedPartitionsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

Taking cumulative cuts and reconstructing the ordered blocks are inverse maps when the label set is nonempty.

**Definition 1.7 (Merging adjacent blocks).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.MergesAdjacent`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.MergesAdjacent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

A partition p merges to q when a monotone surjection from the block indices of p to those of q sends the block of each label in p to its block in q.

**Theorem 1.8 (Adjacent block merges).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.mergesAdjacent_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.mergesAdjacent_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

One partition is obtained from another by merging adjacent blocks exactly when its family of cumulative cuts is contained in the other's family. The merging map on block labels is monotone and surjective.

**Definition 1.9 (Singleton-block partitions).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.permutationAtomsEquiv`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.permutationAtomsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

Permutation flags recover each entry by the difference between successive prefixes, including the final label. Consequently permutations correspond bijectively to atoms.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.MergesAdjacent`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.OrderedPartition`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.cut`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.mergesAdjacent_iff`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.orderedPartitionsEquiv`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.permutationAtomsEquiv`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.rank_toCuts`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.toCuts`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions.toPartition`
- Dependency: [D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags](FaceFlags.md)
