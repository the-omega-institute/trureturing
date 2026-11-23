# Triangle-star graph moves

## Abstract

Triangle-star moves on finite simple graphs and their representation by finite active labels.

**Definition 1.1 (Triangle to star).**

Lean statement: `D5/S3/Combinatorics/Graph/DeltaY/MoveModel.ForwardSpec`

*Formalization.* `D5/S3/Combinatorics/Graph/DeltaY/MoveModel.ForwardSpec` (`✓ std3`).

*Citation.* Zhichen Zhou (2026). *Δ-Y Moves and Partial Steiner Systems*. DOI: [10.48550/arXiv.2609.08963](https://doi.org/10.48550/arXiv.2609.08963). URL: <https://arxiv.org/html/2609.08963v1>.

*Commentary.*

An equivalence from Option of the starting vertex type to the target vertex type identifies the survivors and the fresh center. The three old triangle edges are deleted. The center is joined to precisely the three triangle vertices.

**Definition 1.2 (Star to triangle).**

Lean statement: `D5/S3/Combinatorics/Graph/DeltaY/MoveModel.ReverseSpec`

*Formalization.* `D5/S3/Combinatorics/Graph/DeltaY/MoveModel.ReverseSpec` (`✓ std3`).

*Citation.* Zhichen Zhou (2026). *Δ-Y Moves and Partial Steiner Systems*. DOI: [10.48550/arXiv.2609.08963](https://doi.org/10.48550/arXiv.2609.08963). URL: <https://arxiv.org/html/2609.08963v1>.

*Commentary.*

An equivalence from Option of the surviving vertex type to the starting vertex type identifies the removed center. Its entire neighborhood is the designated triple. Survivor adjacency in the target is the union of old adjacency and all three pairs of the triple.

**Definition 1.3 (Ordinary and strong moves).**

Lean statement: `D5/S3/Combinatorics/Graph/DeltaY/MoveModel.GraphMove`

*Formalization.* `D5/S3/Combinatorics/Graph/DeltaY/MoveModel.GraphMove` (`✓ std3`).

*Citation.* Zhichen Zhou (2026). *Δ-Y Moves and Partial Steiner Systems*. DOI: [10.48550/arXiv.2609.08963](https://doi.org/10.48550/arXiv.2609.08963). URL: <https://arxiv.org/html/2609.08963v1>.

*Commentary.*

Every forward move is allowed in both relations. A strong reverse move requires the three neighbors to form an independent set before the move.

**Theorem 1.4 (Invariance under relabeling).**

Lean statement: `D5/S3/Combinatorics/Graph/DeltaY/MoveModel.transport`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DeltaY/MoveModel.transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhichen Zhou (2026). *Δ-Y Moves and Partial Steiner Systems*. DOI: [10.48550/arXiv.2609.08963](https://doi.org/10.48550/arXiv.2609.08963). URL: <https://arxiv.org/html/2609.08963v1>.

*Commentary.*

Isomorphisms of the initial and final graphs transport a move and preserve its strength. Every finite graph also has a representation by finite active natural labels and unordered edges.

**Theorem 1.5 (Degree of a reverse center).**

Lean statement: `D5/S3/Combinatorics/Graph/DeltaY/MoveModel.source_reverse_degree_three`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DeltaY/MoveModel.source_reverse_degree_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhichen Zhou (2026). *Δ-Y Moves and Partial Steiner Systems*. DOI: [10.48550/arXiv.2609.08963](https://doi.org/10.48550/arXiv.2609.08963). URL: <https://arxiv.org/html/2609.08963v1>.

*Commentary.*

The Option equivalence lists every vertex of the starting graph. The center consequently has precisely the three distinct neighbors in the reverse site.

**Theorem 1.6 (Edge count along strong histories).**

Lean statement: `D5/S3/Combinatorics/Graph/DeltaY/MoveModel.source_strong_edge_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DeltaY/MoveModel.source_strong_edge_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhichen Zhou (2026). *Δ-Y Moves and Partial Steiner Systems*. DOI: [10.48550/arXiv.2609.08963](https://doi.org/10.48550/arXiv.2609.08963). URL: <https://arxiv.org/html/2609.08963v1>.

*Commentary.*

A forward move exchanges three triangle edges for three spokes. A strong reverse move exchanges three spokes for three fresh edges. Hence every finite strong history preserves the number of edges.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DeltaY/MoveModel.ForwardSpec`
- Truth anchor: `D5/S3/Combinatorics/Graph/DeltaY/MoveModel.GraphMove`
- Truth anchor: `D5/S3/Combinatorics/Graph/DeltaY/MoveModel.ReverseSpec`
- Truth anchor: `D5/S3/Combinatorics/Graph/DeltaY/MoveModel.source_reverse_degree_three`
- Truth anchor: `D5/S3/Combinatorics/Graph/DeltaY/MoveModel.source_strong_edge_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/DeltaY/MoveModel.transport`
