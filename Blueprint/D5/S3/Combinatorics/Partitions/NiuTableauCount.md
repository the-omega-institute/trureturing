# Row Deletion for the Shifted Vandermonde Formula

## Abstract

The rational shifted-node formula obeys the same deletion recurrence as the number of standard tableaux of a straight shape.

**Definition 1.1 (Delete a cell).**

$$\operatorname{deleteRow}\left(rows, i\right) = \operatorname{update}\left(rows, i, rows\left(i\right) - 1\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuTableauCount.deleteRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract one in the naturals from the selected row length and retain all k row slots.

**Definition 1.2 (Removable rows).**

$$\operatorname{RemovableRow}\left(rows, i\right) \Leftrightarrow (0 < rows\left(i\right) \land (\forall j \in \operatorname{Fin}\left(k\right),\; i < j \Rightarrow rows\left(j\right) < rows\left(i\right)))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuTableauCount.RemovableRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A removable row is positive and strictly longer than every row below it.

**Definition 1.3 (Shifted row length).**

$$\operatorname{shiftedNode}\left(rows, i\right) = rows\left(i\right) + \operatorname{val}\left(\operatorname{rev}\left(i\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedNode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value of the reversed finite index is the number of row slots below i.

**Definition 1.4 (Vandermonde product).**

$$\forall b \in \operatorname{Fin}\left(k\right) \to \mathbb{Q},\; \operatorname{vandermonde}\left(b\right) = \prod_{i \in \operatorname{Fin}\left(k\right)} \prod_{j \in \operatorname{Ioi}\left(i\right)} (b\left(i\right) - b\left(j\right))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuTableauCount.vandermonde` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inner product ranges over j greater than i.

**Definition 1.5 (Shifted-node formula).**

$$\forall rows \in \operatorname{Fin}\left(k\right) \to \mathbb{N},\; \operatorname{shiftedCount}\left(rows\right) = \frac{\operatorname{cast}\left(\operatorname{factorial}\left(\sum_{j \in \operatorname{Fin}\left(k\right)} rows\left(j\right)\right)\right) \cdot \operatorname{vandermonde}\left((i: \operatorname{Fin}\left(k\right) \mapsto \operatorname{cast}\left(\operatorname{shiftedNode}\left(rows, i\right)\right))\right)}{\prod_{i \in \operatorname{Fin}\left(k\right)} \operatorname{cast}\left(\operatorname{factorial}\left(\operatorname{shiftedNode}\left(rows, i\right)\right)\right)}$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All factorials are formed in the naturals. The displayed product and division are in the rationals.

**Definition 1.6 (Decidability of a removable row).**

$$\forall k \in \mathbb{N},\; \forall rows \in \operatorname{Fin}\left(k\right) \to \mathbb{N},\; \forall i \in \operatorname{Fin}\left(k\right),\; \operatorname{Decidable}\left(\operatorname{RemovableRow}\left(rows, i\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuTableauCount.instDecidableRemovableRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each comparison and the quantifier over the finite row indices are decidable.

**Theorem 1.7 (Empty diagram).**

$$\forall k \in \mathbb{N},\; \operatorname{shiftedCount}\left((i: \operatorname{Fin}\left(k\right) \mapsto 0)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedCount_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed i the differences with later rows run through 1 up to its shifted node and cancel its factorial.

**Theorem 1.8 (One-cell deletion recurrence).**

$$\forall k \in \mathbb{N},\; 2 \le k \Rightarrow \left(\forall rows \in \operatorname{Fin}\left(k\right) \to \mathbb{N},\; \operatorname{Antitone}\left(rows\right) \Rightarrow \left(0 < \sum_{j \in \operatorname{Fin}\left(k\right)} rows\left(j\right) \Rightarrow \operatorname{shiftedCount}\left(rows\right) = \sum_{i \in \operatorname{filter}\left(\operatorname{RemovableRow}\left(rows\right), univ\right)} \operatorname{shiftedCount}\left(\operatorname{deleteRow}\left(rows, i\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedCount_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Vandermonde factors involving each row give its deletion weight. Nonremovable rows have weight zero. Polynomial interpolation shows that the sum of all weights is the total size.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuTableauCount.RemovableRow`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuTableauCount.deleteRow`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuTableauCount.instDecidableRemovableRow`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedCount`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedCount_empty`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedCount_recurrence`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuTableauCount.shiftedNode`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuTableauCount.vandermonde`
