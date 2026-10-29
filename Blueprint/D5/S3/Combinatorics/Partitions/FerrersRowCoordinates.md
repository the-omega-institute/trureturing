# Ferrers Coordinates with Ambient Padding

## Abstract

Column heights and bottom-to-top row lengths describe the same finite board while retaining every ambient zero.

**Definition 1.1 (Padded row profiles).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.Rows`

*Formalization.* `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.Rows` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

Rows(H,U) consists of all weakly decreasing H-tuples with entries in {0,...,U}. The order is from the bottom row to the top row. The dimensions H and U may be zero.

**Definition 1.2 (Source column heights).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.Board`

*Formalization.* `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.Board` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

Board(U,H) consists of all weakly increasing U-tuples of heights in {0,...,H}, in the source left-to-right orientation. An entry b_i occupies exactly the cells (i+1,j+1) with 0 <= j < b_i. Zero heights preserve the fixed column slots.

**Definition 1.3 (Finite diagram).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.diagram`

*Formalization.* `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.diagram` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

The diagram associated with a row profile has cells (i,j) exactly when i < H and j is less than row i. Its rows use zero-based bottom-to-top coordinates; horizontal reflection converts its left-justified rows into the right-aligned source board. Ambient zero rows remain in Rows even though the finite diagram itself has no cells there.

**Definition 1.4 (Padded conjugation).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.conjugate`

*Formalization.* `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.conjugate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

Conjugation transposes the finite diagram and reads its row lengths in the other fixed ambient dimension. It retains both dimensions, so it also retains the trailing zeros omitted by ordinary partition notation.

**Theorem 1.5 (Exact finite cells).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.diagram_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.diagram_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

A cell (i,j) belongs to the finite diagram exactly when i is an ambient row index and j is less than that row length. This also describes rows of length zero without deleting their ambient indices.

**Theorem 1.6 (Recovered row lengths).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.diagram_rowLen`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.diagram_rowLen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

At every ambient row index, the finite diagram has exactly the prescribed row length. This is valid with trailing zero rows; no positivity assumption is required.

**Theorem 1.7 (Conjugation is involutive).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.conjugate_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.conjugate_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

For every nonnegative H and U, conjugating a bounded padded row profile twice gives the original profile, including the zero-dimensional and all-zero cases.

**Definition 1.8 (Exact column and row correspondence).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.boardRowsEquiv`

*Formalization.* `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.boardRowsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

Reverse the weakly increasing source column tuple, form its Young diagram, and transpose. This is a bijection from Board(U,H) to Rows(H,U); the inverse conjugates and reverses. This fixes the source right alignment and does not identify different ambient column slots.

**Theorem 1.9 (The row coordinate counts actual cells).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.board_row_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.board_row_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

For every source board and each ambient row i, the row coordinate equals the number of column indices j whose height exceeds i. Thus the coordinate bijection preserves the number of literal cells in every row, and consequently in each consecutive block of rows.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.Board`
- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.Rows`
- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.boardRowsEquiv`
- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.board_row_count`
- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.conjugate`
- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.conjugate_involutive`
- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.diagram`
- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.diagram_mem`
- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.diagram_rowLen`
