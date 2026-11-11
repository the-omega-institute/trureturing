# Insertion of horizontal and vertical steps

## Abstract

Insertion of horizontal and vertical steps

All degrees p,q are natural numbers. A shuffle is the monotone injective lattice path defined in ShuffleBasic. To insert a first-coordinate step at face index j, first locate the crossing index t, lift the old first coordinate by j.succAbove, and insert the new vertex at t. The second-coordinate construction exchanges the coordinates.

Deleting the inserted vertex recovers the old path composed with the corresponding coface in the product simplex. The pair consisting of the inserted shuffle and its marked insertion index is injective in the original shuffle and face-index data. The index inequalities include the first and last vertices, so the boundary cases use the same construction.

**Definition 1.1 (insertLeftIndex).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftIndex`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftIndex` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The vertex index in the `(p+1, q)`-shuffle's domain where the new left step was inserted. Removing this vertex via `δ` recovers the original shuffle. Equals the number of vertices of `ν` whose first coordinate is `< j`.

In this notation, def insertLeftIndex {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) : Fin (p + q + 2).

**Definition 1.2 (insertRightIndex).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertRightIndex`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertRightIndex` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The vertex index where the new right step was inserted. Equals the number of vertices of `ν` whose second coordinate is `< k`.

In this notation, def insertRightIndex {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) : Fin (p + q + 2).

**Theorem 1.3 (insertLeftIndex_le).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftIndex_le`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftIndex_le` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The insertion index satisfies `t ≤ j + q`: vertices with fst < j have index ≤ (j-1) + q by `coordSum_eq`, so there are at most j + q of them.

In this notation, lemma insertLeftIndex_le {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) : (insertLeftIndex ν j).val ≤ j.val + q.

**Theorem 1.4 (insertLeftIndex_ge).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftIndex_ge`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftIndex_ge` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Lower bound: the left insertion index satisfies `j ≤ t`. Proof: any r with r.val < j has fst(r) ≤ r < j, so the filter includes all r < j.

In this notation, lemma insertLeftIndex_ge {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) : j.val ≤ (insertLeftIndex ν j).val.

**Theorem 1.5 (insertLeftIndex_iff).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftIndex_iff`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftIndex_iff` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The filter `{r | fst(r) < j}` is a downward-closed initial segment: `fst(ν r) < j ↔ r.val < t` where `t = insertLeftIndex`.

In this notation, lemma insertLeftIndex_iff {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) (r : Fin (p + q + 1)) : (ν.1 r).1.val < j.val ↔ r.val < (insertLeftIndex ν j).val.

**Theorem 1.6 (insertRightIndex_iff).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertRightIndex_iff`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertRightIndex_iff` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Symmetric: `snd(ν r) < k ↔ r.val < insertRightIndex`.

In this notation, lemma insertRightIndex_iff {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) (r : Fin (p + q + 1)) : (ν.1 r).2.val < k.val ↔ r.val < (insertRightIndex ν k).val.

**Definition 1.7 (insertLeftStepFun).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftStepFun`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftStepFun` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The underlying piecewise map for `insertLeftStep`: before the insertion point, embed the original vertex via `succAbove j`; at the insertion point, place `(j, t-j)`; after the insertion point, embed the shifted-back vertex via `succAbove j`.

In this notation, noncomputable def insertLeftStepFun {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) : Fin ((p + 1) + q + 1) → Index (p + 1) × Index q.

**Definition 1.8 (insertLeftStep).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftStep`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftStep` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Insert a left step at face index `j`, turning a `(p, q)`-shuffle into a `(p+1, q)`-shuffle. The original path from `(0,0)` to `(p, q)` is embedded into a path from `(0,0)` to `(p+1, q)` by applying `Fin.succAbove j` to the first coordinate and inserting a new left step where the first coordinate crosses `j`.

In this notation, noncomputable def insertLeftStep {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) : Shuffle (p + 1) q.

**Definition 1.9 (insertRightStepFun).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertRightStepFun`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertRightStepFun` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The underlying piecewise map for `insertRightStep`: before the insertion point, embed the original vertex via `succAbove k` on the second coordinate; at the insertion point, place `(t-k, k)`; after the insertion point, embed the shifted-back vertex via `succAbove k`.

In this notation, noncomputable def insertRightStepFun {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) : Fin (p + (q + 1) + 1) → Index p × Index (q + 1).

**Definition 1.10 (insertRightStep).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertRightStep`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertRightStep` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Insert a right step at face index `k`, turning a `(p, q)`-shuffle into a `(p, q+1)`-shuffle. Applies `Fin.succAbove k` to the second coordinate and inserts a new right step where the second coordinate crosses `k`.

In this notation, noncomputable def insertRightStep {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) : Shuffle p (q + 1).

**Theorem 1.11 (insertLeftStep_face).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftStep_face`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftStep_face` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Inserting a left step and removing the inserted vertex recovers the original shuffle with `Fin.succAbove j` applied to the first coordinate. (Purely combinatorial: no `SimplexCategory` or topology needed.)

In this notation, lemma insertLeftStep_face {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) : ∀ (k : Index (p + q)), (insertLeftStep ν j).1 (Fin.succAbove (⟨(insertLeftIndex ν j).val, by omega⟩ : Fin ((p + 1) + q + 1)) (k.cast (by omega))) = (j.succAbove (ν.1 k).1, (ν.1 k).2).

**Theorem 1.12 (insertRightStep_face).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertRightStep_face`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertRightStep_face` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Inserting a right step and removing the inserted vertex recovers the original shuffle with `Fin.succAbove k` applied to the second coordinate.

In this notation, lemma insertRightStep_face {p q : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) : ∀ (i : Index (p + q)), (insertRightStep ν k).1 (Fin.succAbove (⟨(insertRightIndex ν k).val, by omega⟩ : Fin (p + (q + 1) + 1)) (i.cast (by omega))) = ((ν.1 i).1, k.succAbove (ν.1 i).2).

**Theorem 1.13 (insertLeftStep_injective).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftStep_injective`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftStep_injective` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The insert-left map `(j, ν) ↦ (insertLeftStep ν j, insertLeftIndex ν j)` is injective: distinct `(j, ν)` pairs produce distinct `(μ, vertex)` pairs.

In this notation, lemma insertLeftStep_injective {p q : ℕ} (j₁ j₂ : Fin (p + 2)) (ν₁ ν₂ : Shuffle p q) (hμ : insertLeftStep ν₁ j₁ = insertLeftStep ν₂ j₂) (hr : insertLeftIndex ν₁ j₁ = insertLeftIndex ν₂ j₂) : j₁ = j₂ ∧ ν₁ = ν₂.

**Theorem 1.14 (insertRightStep_injective).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertRightStep_injective`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertRightStep_injective` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The insert-right map is injective.

In this notation, lemma insertRightStep_injective {p q : ℕ} (k₁ k₂ : Fin (q + 2)) (ν₁ ν₂ : Shuffle p q) (hμ : insertRightStep ν₁ k₁ = insertRightStep ν₂ k₂) (hr : insertRightIndex ν₁ k₁ = insertRightIndex ν₂ k₂) : k₁ = k₂ ∧ ν₁ = ν₂.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftIndex`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftIndex_ge`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftIndex_iff`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftIndex_le`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftStep`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftStepFun`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftStep_face`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertLeftStep_injective`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertRightIndex`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertRightIndex_iff`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertRightStep`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertRightStepFun`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertRightStep_face`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleInsertion.insertRightStep_injective`
- Dependency: [D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleBasic](ShuffleBasic.md)
