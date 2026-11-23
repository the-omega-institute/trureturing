# The two-color invariant

## Abstract

A two-color invariant forces strong reverse moves above the minimum-degree threshold.

**Theorem 1.1 (Strong reachability at minimum degree six).**

Lean statement: `D5/S3/Combinatorics/Graph/DeltaY/TwoColorInvariant.source_degree_six_histories`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DeltaY/TwoColorInvariant.source_degree_six_histories` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhichen Zhou (2026). *Δ-Y Moves and Partial Steiner Systems*. DOI: [10.48550/arXiv.2609.08963](https://doi.org/10.48550/arXiv.2609.08963). URL: <https://arxiv.org/html/2609.08963v1>.

*Commentary.*

Initially all vertices have the same color. Edges joining different colors weigh two and same-color edges weigh one. The invariant requires weighted degree at least six at each active vertex, monochromatic triangles, and absence of an all-crossing four-cycle.

A forward move colors the new center opposite the triangle. A reverse move preserves the colors of the surviving vertices. In either case, affected survivors exchange weight two for weight two. The triangle and four-cycle conditions prevent a new mixed triangle or a new all-crossing four-cycle.

Induction over the ordinary history gives a strong history with the same successive graphs. The reflexive case is the empty history.

**Theorem 1.2 (Independence at every reachable reverse site).**

Lean statement: `D5/S3/Combinatorics/Graph/DeltaY/TwoColorInvariant.source_reachable_reverse_independent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DeltaY/TwoColorInvariant.source_reachable_reverse_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhichen Zhou (2026). *Δ-Y Moves and Partial Steiner Systems*. DOI: [10.48550/arXiv.2609.08963](https://doi.org/10.48550/arXiv.2609.08963). URL: <https://arxiv.org/html/2609.08963v1>.

*Commentary.*

A center with degree three must have three crossing incident edges to attain weighted degree six. An edge between two of its neighbors would give a mixed triangle. The neighbors therefore form an independent triple.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DeltaY/TwoColorInvariant.source_degree_six_histories`
- Truth anchor: `D5/S3/Combinatorics/Graph/DeltaY/TwoColorInvariant.source_reachable_reverse_independent`
- Dependency: [D5/S3/Combinatorics/Graph/DeltaY/MoveModel](MoveModel.md)
