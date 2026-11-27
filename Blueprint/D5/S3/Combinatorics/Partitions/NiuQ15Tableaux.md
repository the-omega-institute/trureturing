# Tableaux, Deletion and Rectangle Rotation

## Abstract

Standard tableaux, removable-row deletion and the rectangle survival event.

**Definition 1.1 (Straight shapes).**

$$\forall k \in \mathbb{N},\; \forall shape \in \operatorname{RowShape}\left(k\right),\; (shape.rows : \operatorname{Fin}\left(k\right) \to \mathbb{N}) \land \operatorname{Antitone}\left(shape.rows\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.RowShape` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A shape carries the row lengths and a proof that they are antitone, allowing trailing zero lengths.

**Definition 1.2 (Cells of a shape).**

$$\operatorname{Cell}\left(shape\right) = \left\{p : \operatorname{Fin}\left(k\right) \times \mathbb{N} \mid p.2 < shape.rows\left(p.1\right)\right\}$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.Cell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The row and column both start at zero.

**Definition 1.3 (Cell order).**

$$\operatorname{PartialOrder}\left(\operatorname{Cell}\left(shape\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.instPartialOrderCell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The order is the restriction of the coordinatewise partial order on the row and column indices.

**Definition 1.4 (Number of cells).**

$$\operatorname{size}\left(shape\right) = \sum_{i \in \operatorname{Fin}\left(k\right)} shape.rows\left(i\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.size` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum includes every row slot.

**Definition 1.5 (Strictly increasing labels).**

$$\operatorname{Labeling}\left(p, m\right) = \left\{e : p \equiv \operatorname{Fin}\left(m\right) \mid \operatorname{StrictMono}\left(e\right)\right\}$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.Labeling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier p is any preordered type. The labels are a bijection to the zero-based labels in Fin m.

**Definition 1.6 (Standard tableaux).**

$$\operatorname{StandardTableau}\left(shape\right) = \operatorname{Labeling}\left(\operatorname{Cell}\left(shape\right), \operatorname{size}\left(shape\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.StandardTableau` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The strict order condition gives increase along rows and columns.

**Definition 1.7 (Finite tableau type).**

$$\operatorname{Fintype}\left(\operatorname{StandardTableau}\left(shape\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.instFintypeStandardTableau` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The type of strictly increasing bijections between the finite cell and label types is finite.

**Definition 1.8 (Removable rows).**

$$\operatorname{RemovableRow}\left(shape\right) = \left\{i : \operatorname{Fin}\left(k\right) \mid 0 < shape.rows\left(i\right) \land (\forall j \in \operatorname{Fin}\left(k\right),\; i < j \Rightarrow shape.rows\left(j\right) < shape.rows\left(i\right))\right\}$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.RemovableRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The row must be positive and every lower row must be shorter.

**Definition 1.9 (Finite removable row type).**

$$\operatorname{Fintype}\left(\operatorname{RemovableRow}\left(shape\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.instFintypeRemovableRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Removable rows form a subtype of Fin k.

**Definition 1.10 (Shorten a removable row).**

$$\forall i \in \operatorname{RemovableRow}\left(shape\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; (\operatorname{eraseRowEnd}\left(shape, i\right)).rows\left(j\right) = \operatorname{ite}\left(j = i.1, shape.rows\left(j\right) - 1, shape.rows\left(j\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.eraseRowEnd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shortened profile remains antitone. Subtraction is in the naturals.

**Theorem 1.11 (The shortened diagram loses one cell).**

$$\forall k \in \mathbb{N},\; \forall shape \in \operatorname{RowShape}\left(k\right),\; \forall i \in \operatorname{RemovableRow}\left(shape\right),\; \operatorname{size}\left(\operatorname{eraseRowEnd}\left(shape, i\right)\right) + 1 = \operatorname{size}\left(shape\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.size_eraseRowEnd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only the selected positive row loses one cell.

**Theorem 1.12 (Cardinality recurrence).**

$$\forall k \in \mathbb{N},\; \forall shape \in \operatorname{RowShape}\left(k\right),\; 0 < \operatorname{size}\left(shape\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(\operatorname{StandardTableau}\left(shape\right)\right) = \sum_{i \in \operatorname{RemovableRow}\left(shape\right)} \operatorname{Fintype}.\operatorname{card}\left(\operatorname{StandardTableau}\left(\operatorname{eraseRowEnd}\left(shape, i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.card_standardTableau_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing the maximum label gives a bijection with a choice of removable row and a tableau on the shortened diagram.

**Theorem 1.13 (Empty tableau).**

$$\forall k \in \mathbb{N},\; \forall shape \in \operatorname{RowShape}\left(k\right),\; \operatorname{size}\left(shape\right) = 0 \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(\operatorname{StandardTableau}\left(shape\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.card_standardTableau_of_size_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is exactly one bijection between the two empty types.

**Definition 1.14 (Rectangle).**

$$\forall i \in \operatorname{Fin}\left(k + 1\right),\; \operatorname{rectangle}\left(k, n\right).rows\left(i\right) = n$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.rectangle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shape rectangle(k,n) has k + 1 rows, each of length n.

**Theorem 1.15 (Rectangle cardinality).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{size}\left(\operatorname{rectangle}\left(k, n\right)\right) = (k + 1) \cdot n$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.size_rectangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This includes width zero.

**Definition 1.16 (Shortened rectangle).**

$$\forall i \in \operatorname{Fin}\left(k + 1\right),\; \operatorname{rotatedShape}\left(k, n, r\right).rows\left(i\right) = \operatorname{ite}\left(i = \operatorname{last}\left(k\right), n - r, n\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.rotatedShape` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only the bottom row loses r cells, with natural subtraction defined also for r > n.

**Definition 1.17 (First cell of the second row).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall (hn : 0 < n), (\operatorname{secondRowFirst}\left(hn\right) : \operatorname{Cell}\left(\operatorname{rectangle}\left(k + 1, n\right)\right)) \land \operatorname{secondRowFirst}\left(hn\right).1 = (1, 0)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.secondRowFirst` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positive width ensures that the coordinate pair lies in the cell subtype.

**Definition 1.18 (First descent).**

$$\forall (hn : 0 < n), \forall t \in \operatorname{StandardTableau}\left(\operatorname{rectangle}\left(k + 1, n\right)\right),\; \operatorname{firstDescent}\left(hn, t\right) = \operatorname{val}\left(t.1\left(\operatorname{secondRowFirst}\left(hn\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.firstDescent` (`✓ std3`).

*Citation.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

The value of the zero-based label equals the published one-based entry minus one.

**Theorem 1.19 (The first descent lies within the width).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall (hn : 0 < n), \forall t \in \operatorname{StandardTableau}\left(\operatorname{rectangle}\left(k + 1, n\right)\right),\; \operatorname{firstDescent}\left(hn, t\right) \le n$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.firstDescent_le_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Labels before the second-row first entry lie in the top row.

**Theorem 1.20 (Count of the survival event).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall (hn : 0 < n), r \le n \Rightarrow \operatorname{Nat}.\operatorname{card}\left(\left\{t : \operatorname{StandardTableau}\left(\operatorname{rectangle}\left(k + 1, n\right)\right) \mid r \le \operatorname{firstDescent}\left(hn, t\right)\right\}\right) = \operatorname{Fintype}.\operatorname{card}\left(\operatorname{StandardTableau}\left(\operatorname{rotatedShape}\left(k + 1, n, r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.card_rectangle_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Delete the first r cells of the top row and rotate the complement to a straight shape.

**Theorem 1.21 (Empty survival event above the width).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall (hn : 0 < n), n < r \Rightarrow \operatorname{Nat}.\operatorname{card}\left(\left\{t : \operatorname{StandardTableau}\left(\operatorname{rectangle}\left(k + 1, n\right)\right) \mid r \le \operatorname{firstDescent}\left(hn, t\right)\right\}\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.card_rectangle_tail_of_width_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The threshold exceeds every possible descent.

**Theorem 1.22 (Nonempty rectangle tableau type).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; 0 < \operatorname{Fintype}.\operatorname{card}\left(\operatorname{StandardTableau}\left(\operatorname{rectangle}\left(k, n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.rectangle_card_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Row-major labels give a tableau, including at width zero.

**Theorem 1.23 (Partition into a point and the next tail).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall (hn : 0 < n), \forall r \in \mathbb{N},\; \operatorname{Nat}.\operatorname{card}\left(\left\{t : \operatorname{StandardTableau}\left(\operatorname{rectangle}\left(k + 1, n\right)\right) \mid r \le \operatorname{firstDescent}\left(hn, t\right)\right\}\right) = \operatorname{Nat}.\operatorname{card}\left(\left\{t : \operatorname{StandardTableau}\left(\operatorname{rectangle}\left(k + 1, n\right)\right) \mid \operatorname{firstDescent}\left(hn, t\right) = r\right\}\right) + \operatorname{Nat}.\operatorname{card}\left(\left\{t : \operatorname{StandardTableau}\left(\operatorname{rectangle}\left(k + 1, n\right)\right) \mid r + 1 \le \operatorname{firstDescent}\left(hn, t\right)\right\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.card_rectangle_tail_eq_point_add_next` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At threshold r the tableau either has descent r or survives the next threshold.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.Cell`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.Labeling`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.RemovableRow`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.RowShape`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.StandardTableau`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.card_rectangle_tail`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.card_rectangle_tail_eq_point_add_next`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.card_rectangle_tail_of_width_lt`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.card_standardTableau_eq_sum`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.card_standardTableau_of_size_zero`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.eraseRowEnd`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.firstDescent`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.firstDescent_le_width`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.instFintypeRemovableRow`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.instFintypeStandardTableau`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.instPartialOrderCell`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.rectangle`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.rectangle_card_pos`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.rotatedShape`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.secondRowFirst`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.size`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.size_eraseRowEnd`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.size_rectangle`
