# Full selection in nested levels

## Abstract

A recursive cell bijection counts full rook selections in nested complete lower levels.

**Definition 1.1 (The exact lower-level hypothesis).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookLevelSelection.NestedFull`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookLevelSelection.NestedFull` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Levels are indexed from top to bottom. For every earlier level i and later level j, if a cell with column c occurs in level i, then all m cells of column c occur in level j. The column type C is arbitrary finite, with decidable equality. Each level is a finite set of pairs in C times Fin(m).

**Definition 1.2 (Actual full rook selections).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookLevelSelection.Selections`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookLevelSelection.Selections` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A selection is a function choosing one member of each level set, with an injective column projection. Thus every level has exactly one rook and no column has two. Within-level rows are actual Fin(m) values, not a formal weight.

**Theorem 1.3 (The falling level product).**

$$\forall C \in Type,\; [\operatorname{Fintype}\left(C\right)] [\operatorname{DecidableEq}\left(C\right)] \forall m \in Nat,\; \forall n \in Nat,\; \forall L \in \operatorname{Fin}\left(n\right) \to \operatorname{Finset}\left(\operatorname{Prod}\left(C, \operatorname{Fin}\left(m\right)\right)\right),\; \operatorname{NestedFull}\left(m, L\right) \Rightarrow \operatorname{card}\left(\operatorname{Selections}\left(m, L\right)\right) = \operatorname{fallingLevelProduct}\left(m, L\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookLevelSelection.selections_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed fallingLevelProduct(m,L) means the product over i in Fin(n) of card(L(i)) minus m times val(i), using natural truncated subtraction. To prove the count, split a nonempty selection into its top cell and the remaining selection with that entire column removed. The chosen top column contributes exactly m cells to every lower level by NestedFull. Removing it preserves NestedFull and reduces every remaining level cardinality by m. The split and reassembly are inverse on the actual cell functions. Induction gives the product, including empty levels, zero m and impossible selections. The theorem is consumed by the actual Ferrers augmentation in RookAugmentedLevels; it is not an assumption of that application.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/RookLevelSelection.NestedFull`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookLevelSelection.Selections`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookLevelSelection.selections_count`
- Dependency: [D5/S3/Combinatorics/Partitions/RookClassNative](RookClassNative.md)
