# Deletion and Rotation of Standard Tableaux

## Abstract

Maximum-cell deletion for straight tableaux and prefix rotation for rectangular tableaux.

**Definition 1.1 (Straight shapes).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.RowShape`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.RowShape` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

The row lengths are a weakly decreasing function on a finite set of row indices. A cell consists of a row index and a column index strictly below that row's length.

**Definition 1.2 (Standard tableaux).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.StandardTableau`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.StandardTableau` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

A standard tableau is a strictly increasing bijection from the cells in product order to the labels from zero through the number of cells minus one. Adding one to each label gives the paper's entry convention.

**Theorem 1.3 (Row and column increase).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.strictMono_iff_rows_columns`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.strictMono_iff_rows_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

Strict monotonicity of a cell labeling is equivalent to strict increase along every row and every column.

**Theorem 1.4 (Removable rows).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.removable_iff_next`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.removable_iff_next` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

A row is removable exactly when it is nonempty and the next row, if present, has strictly smaller length. The last row needs only positive length.

**Definition 1.5 (Delete the maximum label).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.standardTableauDeleteLast`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.standardTableauDeleteLast` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

For a nonempty shape, delete the cell carrying the largest label. Its row is removable. Inserting the largest label at the end of that row inverts the construction.

**Theorem 1.6 (Cardinality recurrence).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.card_standardTableau_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.card_standardTableau_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

The tableau count of a nonempty shape is the sum of the counts obtained by deleting the last cell of each removable row.

**Theorem 1.7 (Empty tableau).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.card_standardTableau_of_size_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.card_standardTableau_of_size_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

For any row shape of total size zero, the standard tableau count is one.

**Definition 1.8 (First descent).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.firstDescent`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.firstDescent` (`✓ std3`).

*Citation.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

For a positive-width rectangle with at least two rows, the statistic is the entry at row two and column one minus one.

**Theorem 1.9 (Least descent).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.firstDescent_isLeast`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.firstDescent_isLeast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

With positions indexed by the one-based entries, the statistic is the least index whose successor lies in a strictly lower row.

**Definition 1.10 (Shortened rectangle).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.rotatedShape`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.rotatedShape` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

After removing a prefix of length r from the top row and rotating, all rows retain their width except the bottom row, whose length decreases by r.

**Definition 1.11 (Rotate the first-descent survival event).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.rectangleTailRotation`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.rectangleTailRotation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

For a positive-width rectangle with at least two rows and zero through width as the threshold, tableaux with first descent at least the threshold are in bijection with standard tableaux of the shortened shape. The map deletes the prescribed top-row prefix, rotates the remaining cells by 180 degrees and complements their labels.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.RowShape`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.StandardTableau`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.card_standardTableau_eq_sum`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.card_standardTableau_of_size_zero`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.firstDescent`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.firstDescent_isLeast`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.rectangleTailRotation`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.removable_iff_next`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.rotatedShape`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.standardTableauDeleteLast`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.strictMono_iff_rows_columns`
