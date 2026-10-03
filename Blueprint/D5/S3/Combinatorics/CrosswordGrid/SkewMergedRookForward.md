# The Forward Implication

## Abstract

Skew-merged permutations have one or two complete rook placements.

**Theorem 1.1 (The count for a skew-merged permutation).**

Lean statement: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookForward.forward_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookForward.forward_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

For every positive integer n, if a permutation w of zero through n minus one splits into an increasing and a decreasing subsequence, its permutation grid has exactly one or exactly two complete rook placements.

## References

- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookForward.forward_count`
- Dependency: [D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookCenterless](SkewMergedRookCenterless.md)
