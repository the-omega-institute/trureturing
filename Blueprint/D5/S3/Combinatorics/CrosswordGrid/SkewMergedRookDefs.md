# Skew-Merged Permutations and Rook Placements

## Abstract

Skew-merged permutations split into an increasing and a decreasing subsequence; their permutation grids are conjectured to have one or two complete rook placements.

**Definition 1.1 (Increasing and decreasing subsequences).**

Lean statement: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDefs.SkewMerged`

*Formalization.* `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDefs.SkewMerged` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Let w be a permutation of the positions zero through n minus one. It is skew-merged if there is a set S of positions such that, for any i and j in S with i less than j, w(i) is less than w(j), and, for any i and j outside S with i less than j, w(j) is less than w(i). Either subsequence may be empty.

**Definition 1.2 (The conjectured equivalence).**

Lean statement: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDefs.claim`

*Formalization.* `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

For every positive integer n and every permutation w of zero through n minus one, the n by n grid with black cells (i, w(i)) has exactly one or exactly two complete rook placements if and only if w is skew-merged. A complete rook placement is a set of white cells meeting each maximal horizontal white interval and each maximal vertical white interval exactly once.

## References

- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDefs.SkewMerged`
- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDefs.claim`
- Dependency: [D5/S3/Combinatorics/CrosswordPermutationGridRefutation](../CrosswordPermutationGridRefutation.md)
