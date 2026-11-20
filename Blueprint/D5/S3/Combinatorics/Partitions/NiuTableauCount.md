# Row Deletion for the Shifted Vandermonde Formula

## Abstract

The rational shifted-node formula obeys the same deletion recurrence as the number of standard tableaux of a straight shape.

**Definition 1.1 (Delete a cell).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuTableauCount.deleteRow`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuTableauCount.deleteRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract one, with natural-number truncation, from the selected row length and retain all k row slots.

**Definition 1.2 (Removable rows).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuTableauCount.RemovableRow`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuTableauCount.RemovableRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A row is removable when its length is positive and strictly greater than the length of every later row.

**Definition 1.3 (Shifted row length).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedNode`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedNode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Add the number of row slots below a row to its length.

**Definition 1.4 (Vandermonde product).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuTableauCount.vandermonde`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuTableauCount.vandermonde` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the differences b_i - b_j for all pairs of row indices i < j.

**Definition 1.5 (Shifted-node formula).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedCount`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For row lengths lambda indexed from zero, set b_i = lambda_i + k - 1 - i and let N be the sum of the row lengths. The formula is N! times the product of b_i - b_j over i < j, divided by the product of b_i! over all rows, in the rational numbers.

**Theorem 1.6 (Empty diagram).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedCount_empty`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedCount_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k, the empty profile has value one. For fixed i the differences b_i - b_j with j > i run through 1 up to b_i, so their product cancels b_i!.

**Theorem 1.7 (One-cell deletion recurrence).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedCount_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedCount_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least two and weakly decreasing row lengths of positive total size, the formula is the sum of its values after deleting one cell from each removable row. The factors of the Vandermonde product involving that row give its deletion weight. A nonremovable row has weight zero. Polynomial interpolation shows that the sum of all weights is N, which cancels the ratio N! / (N - 1)!.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuTableauCount.RemovableRow`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuTableauCount.deleteRow`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedCount`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedCount_empty`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedCount_recurrence`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedNode`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuTableauCount.vandermonde`
