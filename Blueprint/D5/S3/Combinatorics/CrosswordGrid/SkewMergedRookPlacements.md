# Existence and Uniqueness of Complete Placements

## Abstract

Every permutation grid has a complete placement; overlapping increasing and decreasing covers force uniqueness.

**Theorem 1.1 (Existence of a complete placement).**

Lean statement: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookPlacements.count_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookPlacements.count_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

For every positive integer n and every permutation w of zero through n minus one, the number of complete rook placements of its permutation grid is strictly positive.

**Theorem 1.2 (An overlapping monotone cover).**

Lean statement: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookPlacements.overlapping_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookPlacements.overlapping_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Let n be positive and let two sets of positions cover all positions of a permutation w. Suppose that the values on the first set increase with position and the values on the second set decrease with position. If some position belongs to both sets, the permutation grid of w has exactly one complete rook placement.

## References

- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookPlacements.count_positive`
- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookPlacements.overlapping_count`
- Dependency: [D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDeletions](SkewMergedRookDeletions.md)
