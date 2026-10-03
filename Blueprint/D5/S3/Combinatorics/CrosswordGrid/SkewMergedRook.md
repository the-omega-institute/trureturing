# Skew-Merged Permutations Are Exactly Those With One or Two Placements

## Abstract

A permutation grid has exactly one or two complete rook placements if and only if its permutation is skew-merged.

**Theorem 1.1 (The skew-merged equivalence).**

Lean statement: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRook.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRook.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

For every positive integer n and every permutation w of zero through n minus one, the n by n grid with black cells (i, w(i)) has exactly one or exactly two complete rook placements if and only if the positions of w split into a set on which its values increase and a complementary set on which its values decrease. Complete placements meet every maximal horizontal white interval and every maximal vertical white interval exactly once. This is Conjecture 3.9 of Lewis and Won.

## References

- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRook.result`
- Dependency: [D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookBoundary](SkewMergedRookBoundary.md)
- Dependency: [D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookForward](SkewMergedRookForward.md)
