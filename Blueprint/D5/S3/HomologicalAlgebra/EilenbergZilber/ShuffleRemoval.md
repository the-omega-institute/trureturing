# Boundary vertices and inverse insertion

## Abstract

Boundary vertices and inverse insertion

A diagonal vertex of a shuffle is an interior corner: deleting it merges unlike steps and increases both coordinates. A left vertex has the complementary first-coordinate behavior; a right vertex has the second-coordinate behavior. Endpoints are included through the explicit endpoint clauses in these predicates.

The finite deletion map finRemove inverts succAbove away from the removed point. At a left vertex the first-coordinate value occurs nowhere else, so deleting its row and vertex produces a smaller injective monotone path. The right construction follows by swapping coordinates. Every nondiagonal vertex of a (p+1,q+1)-shuffle is uniquely represented in one of the two insertion families, with the original degree and face indices retained.

**Definition 1.1 (isDiagonalVertex).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.isDiagonalVertex`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.isDiagonalVertex` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

A `(μ, r)` pair is a **diagonal term** if vertex `r` has one adjacent left step and one adjacent right step (in either order LR or RL). Boundary vertices (r = 0 or r = last) are never diagonal.

In this notation, def isDiagonalVertex {p q : ℕ} (μ : Shuffle p q) (r : Index (p + q)) : Prop.

**Definition 1.2 (decidablePredIsDiagonalVertex).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.decidablePredIsDiagonalVertex`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.decidablePredIsDiagonalVertex` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The two adjacent step types determine a decidable diagonal-vertex predicate.

In this notation, instance decidablePredIsDiagonalVertex {p q : ℕ} (μ : Shuffle (p) (q)) : DecidablePred (isDiagonalVertex μ).

**Theorem 1.3 (insertLeftStep_not_diagonal).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertLeftStep_not_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertLeftStep_not_diagonal` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Left insertion always produces a non-diagonal vertex: every existing adjacent step is left. Interior insertions have the LL pattern; an endpoint insertion has only its one adjacent edge.

In this notation, lemma insertLeftStep_not_diagonal {p q : ℕ} (ν : Shuffle p (q)) (j : Fin (p + 2)) : ¬isDiagonalVertex (insertLeftStep ν j) ((insertLeftIndex ν j).cast (by omega)).

**Theorem 1.4 (insertRightStep_not_diagonal).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertRightStep_not_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertRightStep_not_diagonal` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Right insertion always produces a non-diagonal vertex: every existing adjacent step is right. Interior insertions have the RR pattern; an endpoint insertion has only its one adjacent edge.

In this notation, lemma insertRightStep_not_diagonal {p q : ℕ} (ν : Shuffle (p + 1) q) (k : Fin (q + 2)) : ¬isDiagonalVertex (insertRightStep ν k) ((insertRightIndex ν k).cast (by omega)).

**Definition 1.5 (isLeftVertex).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.isLeftVertex`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.isLeftVertex` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

A vertex `r` is a "left vertex" if every existing adjacent step is left. Both steps are tested at an interior vertex, only the existing edge at an endpoint, and the predicate is vacuously true when the path has no edges.

In this notation, def isLeftVertex {p q : ℕ} (μ : Shuffle p q) (r : Fin (p + q + 1)) : Prop.

**Definition 1.6 (isRightVertex).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.isRightVertex`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.isRightVertex` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

A vertex `r` is a "right vertex" if every existing adjacent step is right. Both steps are tested at an interior vertex, only the existing edge at an endpoint, and the predicate is vacuously true when the path has no edges.

In this notation, def isRightVertex {p q : ℕ} (μ : Shuffle p q) (r : Fin (p + q + 1)) : Prop.

**Definition 1.7 (finRemove).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.finRemove`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.finRemove` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Inverse of `Fin.succAbove p`: maps `i` to `j` such that `p.succAbove j = i`, assuming `i ≠ p`.

In this notation, def finRemove {n : ℕ} (p : Fin (n + 2)) (i : Fin (n + 2)) : Fin (n + 1).

**Definition 1.8 (removeLeftFun).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeLeftFun`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeLeftFun` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Removing a left step at `r` (assuming `isLeftVertex μ r`).

In this notation, def removeLeftFun {p q : ℕ} (μ : Shuffle (p + 1) q) (r : Fin (p + q + 2)) : Index (p + q) → Index p × Index q.

**Definition 1.9 (removeRightFun).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeRightFun`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeRightFun` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Removing a right step at `r` (assuming `isRightVertex μ r`).

In this notation, def removeRightFun {p q : ℕ} (μ : Shuffle p (q + 1)) (r : Fin (p + q + 2)) : Index (p + q) → Index p × Index q.

**Theorem 1.10 (succAbove_finRemove).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.succAbove_finRemove`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.succAbove_finRemove` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Removing a value different from p and reinserting the skipped value p recovers the original finite index.

In this notation, lemma succAbove_finRemove {n : ℕ} (p : Fin (n + 2)) (i : Fin (n + 2)) (h : i ≠ p) : p.succAbove (finRemove p i) = i.

**Theorem 1.11 (finRemove_strictMono_on).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.finRemove_strictMono_on`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.finRemove_strictMono_on` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The finite deletion map is strictly monotone on the complement of its removed value.

In this notation, lemma finRemove_strictMono_on {n : ℕ} (p : Fin (n + 2)) : StrictMonoOn (finRemove p) {i | i ≠ p}.

**Theorem 1.12 (ne_fst_of_isLeftVertex).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.ne_fst_of_isLeftVertex`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.ne_fst_of_isLeftVertex` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

At a left vertex the first-coordinate value differs from that of every other vertex.

In this notation, lemma ne_fst_of_isLeftVertex {p q : ℕ} {μ : Shuffle (p + 1) q} {r : Index ((p + 1) + q)} (h : isLeftVertex μ r) (k : Index ((p + 1) + q)) (hkr : k ≠ r) : (μ.1 k).1 ≠ (μ.1 r).1.

**Theorem 1.13 (ne_snd_of_isRightVertex).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.ne_snd_of_isRightVertex`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.ne_snd_of_isRightVertex` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

At a right vertex the second-coordinate value differs from that of every other vertex.

In this notation, lemma ne_snd_of_isRightVertex {p q : ℕ} {μ : Shuffle p (q + 1)} {r : Index (p + (q + 1))} (h : isRightVertex μ r) (k : Index (p + (q + 1))) (hkr : k ≠ r) : (μ.1 k).2 ≠ (μ.1 r).2.

**Theorem 1.14 (removeLeft_is_shuffle).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeLeft_is_shuffle`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeLeft_is_shuffle` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Deleting a left vertex and its first-coordinate level gives a strictly monotone path.

In this notation, lemma removeLeft_is_shuffle {p q : ℕ} {μ : Shuffle (p + 1) q} {r : Fin (p + q + 2)} (h : isLeftVertex μ (r.cast (by omega))) : StrictMono (removeLeftFun μ r).

**Theorem 1.15 (removeRight_is_shuffle).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeRight_is_shuffle`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeRight_is_shuffle` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Deleting a right vertex and its second-coordinate level gives a strictly monotone path.

In this notation, lemma removeRight_is_shuffle {p q : ℕ} {μ : Shuffle p (q + 1)} {r : Fin (p + q + 2)} (h : isRightVertex μ (r.cast (by omega))) : StrictMono (removeRightFun μ r).

**Definition 1.16 (removeLeft).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeLeft`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeLeft` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The shuffle obtained by removing a left step.

In this notation, def removeLeft {p q : ℕ} (μ : Shuffle (p + 1) q) (r : Fin (p + q + 2)) (h : isLeftVertex μ (r.cast (by omega))) : Shuffle p q.

**Definition 1.17 (removeRight).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeRight`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeRight` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The shuffle obtained by removing a right step.

In this notation, def removeRight {p q : ℕ} (μ : Shuffle p (q + 1)) (r : Fin (p + q + 2)) (h : isRightVertex μ (r.cast (by omega))) : Shuffle p q.

**Theorem 1.18 (finRemove_val_lt_iff).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.finRemove_val_lt_iff`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.finRemove_val_lt_iff` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Away from the removed value, lying below the new gap is equivalent to lying below the old removed index.

In this notation, lemma finRemove_val_lt_iff {n : ℕ} {p : Fin (n + 2)} {i : Fin (n + 2)} (h : i ≠ p) : (finRemove p i).val < p.val ↔ i < p.

**Theorem 1.19 (insertIndex_removeLeft).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertIndex_removeLeft`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertIndex_removeLeft` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The insertion index of a path obtained by left removal is exactly the removed vertex index.

In this notation, lemma insertIndex_removeLeft {p q : ℕ} {μ : Shuffle (p + 1) q} {r : Fin (p + q + 2)} (h : isLeftVertex μ (r.cast (by omega))) : insertLeftIndex (removeLeft μ r h) (μ.1 (r.cast (by omega))).1 = r.cast (by omega).

**Theorem 1.20 (insertLeft_removeLeft).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertLeft_removeLeft`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertLeft_removeLeft` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Left insertion at the removed first-coordinate value recovers the original path.

In this notation, lemma insertLeft_removeLeft {p q : ℕ} {μ : Shuffle (p + 1) q} {r : Fin (p + q + 2)} (h : isLeftVertex μ (r.cast (by omega))) : insertLeftStep (removeLeft μ r h) (μ.1 (r.cast (by omega))).1 = μ.

**Theorem 1.21 (insertIndex_removeRight).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertIndex_removeRight`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertIndex_removeRight` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The insertion index of a path obtained by right removal is exactly the removed vertex index.

In this notation, lemma insertIndex_removeRight {p q : ℕ} {μ : Shuffle p (q + 1)} {r : Fin (p + q + 2)} (h : isRightVertex μ (r.cast (by omega))) : insertRightIndex (removeRight μ r h) (μ.1 (r.cast (by omega))).2 = r.cast (by omega).

**Theorem 1.22 (isRightVertex_swap).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.isRightVertex_swap`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.isRightVertex_swap` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Right vertices become left vertices under coordinate exchange.

In this notation, lemma isRightVertex_swap {p q : ℕ} {μ : Shuffle p q} {r : Fin (p + q + 1)} : isRightVertex μ r ↔ isLeftVertex μ.swap (r.cast (by omega)).

**Theorem 1.23 (removeRight_eq_swap_removeLeft).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeRight_eq_swap_removeLeft`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeRight_eq_swap_removeLeft` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Right removal is coordinate exchange, followed by left removal and coordinate exchange back.

In this notation, lemma removeRight_eq_swap_removeLeft {p q : ℕ} (μ : Shuffle p (q + 1)) (r : Fin (p + q + 2)) (h : isRightVertex μ (r.cast (by omega))) : removeRight μ r h = (removeLeft μ.swap (r.cast (by omega)) (isRightVertex_swap.mp h)).swap.

**Theorem 1.24 (not_diagonal_iff_left_or_right).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.not_diagonal_iff_left_or_right`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.not_diagonal_iff_left_or_right` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

A nondiagonal vertex belongs to at least one of the left and right vertex classes.

In this notation, lemma not_diagonal_iff_left_or_right {p q : ℕ} {μ : Shuffle (p + 1) (q + 1)} {r : Fin (p + q + 3)} : ¬isDiagonalVertex μ (r.cast (by omega)) ↔ isLeftVertex μ (r.cast (by omega)) ∨ isRightVertex μ (r.cast (by omega)).

**Theorem 1.25 (nondiag_mem_insertLeft_or_insertRight).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.nondiag_mem_insertLeft_or_insertRight`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.nondiag_mem_insertLeft_or_insertRight` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Each nondiagonal marked vertex is the insertion index of a left or right insertion into a smaller shuffle.

In this notation, lemma nondiag_mem_insertLeft_or_insertRight {p q : ℕ} (μ : Shuffle (p + 1) (q + 1)) (r : Index ((p + 1) + (q + 1))) (hr : ¬isDiagonalVertex μ r) : (∃ (j : Fin (p + 2)) (ν : Shuffle p (q + 1)), μ = insertLeftStep ν j ∧ (insertLeftIndex ν j).val = r.val) ∨ (∃ (k : Fin (q + 2)) (ν : Shuffle (p + 1) q), μ = insertRightStep ν k ∧ (insertRightIndex ν k).val = r.val).

**Theorem 1.26 (insertLeftStep_isLeftType).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertLeftStep_isLeftType`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertLeftStep_isLeftType` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Left insertion produces a left-type vertex: the step at (or just before) the inserted vertex is a left step. Here `isLeftType` checks `isLeftStep` at index `min r.val ((p+1)+(q)-1)`.

In this notation, lemma insertLeftStep_isLeftType {p q : ℕ} (ν : Shuffle p (q)) (j : Fin (p + 2)) : isLeftStep (insertLeftStep ν j) ⟨min (insertLeftIndex ν j).val ((p + 1) + (q) - 1), by omega⟩.

**Theorem 1.27 (insertRightStep_not_isLeftType).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertRightStep_not_isLeftType`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertRightStep_not_isLeftType` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Right insertion produces a non-left-type vertex: the step at (or just before) the inserted vertex is a right step, not a left step.

In this notation, lemma insertRightStep_not_isLeftType {p q : ℕ} (ν : Shuffle (p) q) (k : Fin (q + 2)) : ¬isLeftStep (insertRightStep ν k) ⟨min (insertRightIndex ν k).val ((p) + (q + 1) - 1), by omega⟩.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.decidablePredIsDiagonalVertex`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.finRemove`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.finRemove_strictMono_on`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.finRemove_val_lt_iff`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertIndex_removeLeft`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertIndex_removeRight`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertLeftStep_isLeftType`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertLeftStep_not_diagonal`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertLeft_removeLeft`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertRightStep_not_diagonal`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.insertRightStep_not_isLeftType`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.isDiagonalVertex`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.isLeftVertex`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.isRightVertex`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.isRightVertex_swap`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.ne_fst_of_isLeftVertex`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.ne_snd_of_isRightVertex`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.nondiag_mem_insertLeft_or_insertRight`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.not_diagonal_iff_left_or_right`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeLeft`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeLeftFun`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeLeft_is_shuffle`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeRight`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeRightFun`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeRight_eq_swap_removeLeft`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.removeRight_is_shuffle`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval.succAbove_finRemove`
- Dependency: [D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns](ShuffleSigns.md)
