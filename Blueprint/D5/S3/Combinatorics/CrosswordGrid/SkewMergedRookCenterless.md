# Cuts for a Centerless Skew-Merged Permutation

## Abstract

A skew-merged permutation with no overlapping monotone cover has four nonempty regions separated by an interior row cut and an interior column cut.

**Theorem 1.1 (Four regions and forced neighboring cells).**

Lean statement: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookCenterless.centerless_cuts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookCenterless.centerless_cuts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Let n be positive and let S be a set of positions of a permutation w, increasing in value on S and decreasing in value outside S. Suppose that no increasing set and decreasing set covering all positions have a common position. There are integers r and c strictly between zero and n such that a position i belongs to S exactly when i less than r is equivalent to w(i) less than c. Each of the four combinations of the inequalities i less than r and w(i) less than c contains a position. Either w(r - 1) is less than c - 1, w(r) is greater than c, the position of value c - 1 is greater than r, and the position of value c is less than r - 1; or w(r - 1) is greater than c, w(r) is less than c - 1, the position of value c - 1 is less than r - 1, and the position of value c is greater than r. Every complete placement contains each cell immediately to the left of a black cell of value less than c, immediately to the right of a black cell of value at least c, immediately above a black cell of row less than r, or immediately below a black cell of row at least r, whenever the indicated neighboring cell lies in the grid.

## References

- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookCenterless.centerless_cuts`
- Dependency: [D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookPlacements](SkewMergedRookPlacements.md)
- Dependency: [D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookRegions](SkewMergedRookRegions.md)
