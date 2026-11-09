# Finite labels and exact adjacency rows

## Abstract

Finite labels and exact adjacency rows

**Definition 1.1 (An edge-list graph).**

Lean statement: `D5/S3/Geometry/KingFiniteReplay/FiniteLabels.listGraph`

*Formalization.* `D5/S3/Geometry/KingFiniteReplay/FiniteLabels.listGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The finite graph on a specified finite set of natural labels has exactly the unordered pairs listed as edges, with loops excluded.

**Theorem 1.2 (Exact bit-row meaning).**

Lean statement: `D5/S3/Geometry/KingFiniteReplay/FiniteLabels.rowBits_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KingFiniteReplay/FiniteLabels.rowBits_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Bit y in row x is set precisely when an orientation of the pair x,y occurs in the original edge list.

**Definition 1.3 (Verified row evaluation).**

Lean statement: `D5/S3/Geometry/KingFiniteReplay/FiniteLabels.cachedAdjDecidable`

*Formalization.* `D5/S3/Geometry/KingFiniteReplay/FiniteLabels.cachedAdjDecidable` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

An equality proof between cached rows and the original row function yields a decision procedure for the original graph adjacency; the graph definition is unchanged.

**Definition 1.4 (Old and fresh labels).**

Lean statement: `D5/S3/Geometry/KingFiniteReplay/FiniteLabels.sumLabels`

*Formalization.* `D5/S3/Geometry/KingFiniteReplay/FiniteLabels.sumLabels` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Injective old and fresh label functions with disjoint images, all landing in the target finite set and jointly covering it, give an equivalence from their sum carrier to the target labels.

**Theorem 1.5 (Graph equality after relabeling).**

Lean statement: `D5/S3/Geometry/KingFiniteReplay/FiniteLabels.map_eq_of_forward`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KingFiniteReplay/FiniteLabels.map_eq_of_forward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

An adjacency equivalence checked in the forward direction identifies the relabeled graph with the given target graph.

## References

- Truth anchor: `D5/S3/Geometry/KingFiniteReplay/FiniteLabels.cachedAdjDecidable`
- Truth anchor: `D5/S3/Geometry/KingFiniteReplay/FiniteLabels.listGraph`
- Truth anchor: `D5/S3/Geometry/KingFiniteReplay/FiniteLabels.map_eq_of_forward`
- Truth anchor: `D5/S3/Geometry/KingFiniteReplay/FiniteLabels.rowBits_spec`
- Truth anchor: `D5/S3/Geometry/KingFiniteReplay/FiniteLabels.sumLabels`
- Dependency: [D5/S3/Geometry/FiniteGraphSuspensionMoves](../FiniteGraphSuspensionMoves.md)
