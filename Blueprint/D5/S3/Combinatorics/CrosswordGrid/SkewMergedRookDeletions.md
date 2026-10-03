# Placement Counts Under Extreme Insertions

## Abstract

Adding a final maximum, or inserting an interior maximum under a specified ordering condition, cannot decrease the rook-placement count.

**Theorem 1.1 (Appending a maximum).**

Lean statement: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDeletions.corner_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDeletions.corner_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Let n be positive and let u be a permutation of zero through n minus one. Let w be a permutation of zero through n with w(n) equal to n and w(i) equal to u(i) for every i less than n. The number of complete rook placements of the grid of u is at most the number for the grid of w.

**Theorem 1.2 (Inserting an interior maximum).**

Lean statement: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDeletions.interior_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDeletions.interior_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Let n be positive, let u be a permutation of zero through n minus one, and let w be a permutation of zero through n. Choose a position p strictly between zero and n with w(p) equal to n. Deleting that position from w, without changing the other values, gives u. If the position of value n minus one in w is less than p, the number of complete rook placements of the grid of u is at most the number for the grid of w.

## References

- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDeletions.corner_lift`
- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDeletions.interior_lift`
- Dependency: [D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookWords](SkewMergedRookWords.md)
