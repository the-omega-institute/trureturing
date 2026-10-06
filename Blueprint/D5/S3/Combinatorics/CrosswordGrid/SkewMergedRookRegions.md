# Split Graphs and Forbidden Permutation Patterns

## Abstract

A graph without the three forbidden induced configurations splits into a clique and an independent set, and skew-merged permutations are exactly the 2143- and 3412-avoiders.

**Theorem 1.1 (A clique and an independent set).**

Lean statement: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookRegions.graph_split_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookRegions.graph_split_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Let n be positive and let G be a simple graph on zero through n minus one. Suppose that G has no induced subgraph consisting of two disjoint edges, no induced four-cycle and no induced five-cycle. There is a set of vertices forming a clique such that no two vertices outside that set are adjacent.

**Theorem 1.2 (Avoiding 2143 and 3412).**

Lean statement: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookRegions.skew_iff_avoidance`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookRegions.skew_iff_avoidance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

For positive n, a permutation w is skew-merged if and only if it avoids the classical patterns 2143 and 3412. Explicitly, for every four positions a less than b less than c less than d, neither w(b) less than w(a) less than w(d) less than w(c) nor w(c) less than w(d) less than w(a) less than w(b) holds.

## References

- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookRegions.graph_split_criterion`
- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookRegions.skew_iff_avoidance`
- Dependency: [D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDefs](SkewMergedRookDefs.md)
