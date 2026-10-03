# Words and Symmetries of Permutation Grids

## Abstract

The words of a permutation grid are determined by the sides of its black cells, and every complete placement has the same cardinality.

**Theorem 1.1 (Horizontal words and vertical word labels).**

Lean statement: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookWords.word_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookWords.word_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Let n be positive and w a permutation of zero through n minus one. Two white cells share a horizontal word exactly when they have the same row and lie on the same side of that row's black cell. There is a word representation whose vertical word label at (i, j) is twice j when i is less than the position of value j in w, and twice j plus one otherwise.

**Theorem 1.2 (The size of a complete placement).**

Lean statement: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookWords.placement_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookWords.placement_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

For positive n, every complete rook placement of the permutation grid of w contains exactly twice n minus two cells.

**Theorem 1.3 (Forced cells along a record prefix).**

Lean statement: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookWords.record_prefix_forces_neighbor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookWords.record_prefix_forces_neighbor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Let n be positive, w a permutation, R a complete placement and b a nonnegative integer. Suppose that every column j less than b has its black cell either above all black cells in later columns less than b or below all of them. Whenever k plus one equals j and j is less than b, R contains the cell in column k and in the row of the black cell in column j.

**Theorem 1.4 (Transposition and reflections).**

Lean statement: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookWords.symmetries`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookWords.symmetries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

For positive n, inverting a permutation, complementing its values, or reversing its positions preserves both its rook-placement count and the property of being skew-merged. Transposing every cell of a complete placement gives a complete placement for the inverse permutation. Reflecting its columns gives a complete placement for the value complement, and reflecting its rows gives a complete placement for the position reversal.

## References

- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookWords.placement_card`
- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookWords.record_prefix_forces_neighbor`
- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookWords.symmetries`
- Truth anchor: `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookWords.word_structure`
- Dependency: [D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDefs](SkewMergedRookDefs.md)
