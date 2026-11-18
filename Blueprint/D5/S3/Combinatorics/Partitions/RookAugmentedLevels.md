# Actual augmented Ferrers levels

## Abstract

Arbitrary Ferrers input with auxiliary full columns realizes the product side of level-total factorization.

**Definition 1.1 (Disjoint source and auxiliary columns).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.Columns`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.Columns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Columns(B,t) is the disjoint sum of the original positive-column positions and t auxiliary positions. Original and auxiliary columns can never be confused by their labels.

**Definition 1.2 (Literal augmented cells).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.level`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.level` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For N levels indexed from the top, position p has bottom-up index N-1-p. An original column i contributes exactly the within-level rows r with m(N-1-p)+r below its actual source height. Every auxiliary column contributes all m within-level rows. For lengths below the board's full height, this definition counts its actual first N bottom-up levels; the registered common lengths cover the whole board.

**Theorem 1.3 (The level-total product on actual cells).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall t \in Nat,\; \forall b \in PositiveColumns,\; \operatorname{card}\left(\operatorname{Selections}\left(m, \operatorname{level}\left(m, n, t, b\right)\right)\right) = \operatorname{levelProduct}\left(m, n, t, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.augmented_selections_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m,N,t and every normalized original board B, the number of full Selections of the actual augmented levels equals levelProduct(m,N,t,B). This product ranges over i in Fin(N), with factor columnLevel(m,B,N-1-i) plus mt minus mi in natural truncated subtraction. No singleton hypothesis is used. If a column contains a cell in an upper level, bottom justification gives all m cells in that column in a lower level. Auxiliary columns are full by construction. The generic selections_count theorem therefore applies, and a direct finite cell count identifies each level cardinality with columnLevel plus mt.

The first remaining counting obligation is the other count of these same augmented selections. For every positive m, normalized B, N at least area(B)+1 and every natural t, it must equal the sum over k from zero through N of rookCount(m,B,k) times m to the power N-k times the descending factorial of t of length N-k. This requires a bijection obtained by retaining the actual original-board rook subset and completing its unused levels in distinct auxiliary columns, with all within-level row choices. That bijection and identity have not been proved here. After them, an infinite family of evaluations can yield the native level-total polynomial identity. Neither this product theorem nor the separate root-family weight count is the full universal K=Q theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.Columns`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.augmented_selections_count`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.level`
- Dependency: [D5/S3/Combinatorics/Partitions/RookLevelSelection](RookLevelSelection.md)
