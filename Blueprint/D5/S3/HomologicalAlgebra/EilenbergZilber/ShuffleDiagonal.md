# Cancellation at diagonal vertices

## Abstract

Cancellation at diagonal vertices

Let μ be a (p,q)-shuffle and r a diagonal vertex. Both neighboring vertices exist. Interchange the two different steps adjacent to r, keeping all other vertices fixed; this defines swapDiagonalSteps. The new middle vertex is the opposite corner of the same unit square.

The replacement path remains monotone and injective. Its two adjacent step types are toggled, the marked vertex remains diagonal, and repeating the operation recovers μ. The inversion counts have opposite parity, so the integer signs are negatives of one another. There are no fixed points. This marked-vertex involution cancels the remaining diagonal terms of the shuffle boundary sum.

**Theorem 1.1 (isDiagonalVertex_bounds).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.isDiagonalVertex_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.isDiagonalVertex_bounds` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Extract the two facts from `isDiagonalVertex`: `0 < r` and `r < p+q`.

In this notation, lemma isDiagonalVertex_bounds {p q : ℕ} {μ : Shuffle p q} {r : Index (p + (q))} (hr : isDiagonalVertex μ r) : 0 < r.val ∧ r.val < (p) + (q).

**Theorem 1.2 (diagonal_left_fst_pos).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.diagonal_left_fst_pos`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.diagonal_left_fst_pos` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

At a diagonal vertex with a left step at `r-1`, the shuffle step from `r-1` to `r` increments fst, giving `μ(r).1 ≥ 1`.

In this notation, lemma diagonal_left_fst_pos {p q : ℕ} {μ : Shuffle (p) (q)} {r : Index (p + (q))} (hr : isDiagonalVertex μ r) (hL : isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩) : 0 < (μ.1 r).1.val.

**Theorem 1.3 (diagonal_right_snd_pos).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.diagonal_right_snd_pos`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.diagonal_right_snd_pos` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

At a diagonal vertex with a right step at `r-1`, the shuffle step from `r-1` to `r` increments snd, giving `μ(r).2 ≥ 1`.

In this notation, lemma diagonal_right_snd_pos {p q : ℕ} {μ : Shuffle (p) (q)} {r : Index (p + (q))} (hr : isDiagonalVertex μ r) (hR : ¬isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩) : 0 < (μ.1 r).2.val.

**Definition 1.4 (swapDiagonalStepsFun).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalStepsFun`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalStepsFun` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The underlying function for `swapDiagonalSteps`: agrees with `μ` everywhere except at vertex `r`, where the step type is swapped. - LR diagonal (left then right): `μ(r)` becomes `(μ(r).1 - 1, μ(r).2 + 1)` - RL diagonal (right then left): `μ(r)` becomes `(μ(r).1 + 1, μ(r).2 - 1)`

In this notation, def swapDiagonalStepsFun {p q : ℕ} (μ : Shuffle p q) (r : Index (p + (q))) (hr : isDiagonalVertex μ r) : Index ((p ) + (q )) → Index (p) × Index (q).

**Theorem 1.5 (swapDiagonalStepsFun_monotone).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalStepsFun_monotone`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalStepsFun_monotone` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The corner-swapped vertex function is monotone.

In this notation, lemma swapDiagonalStepsFun_monotone {p q : ℕ} (μ : Shuffle (p) (q)) (r : Index (p + (q))) (hr : isDiagonalVertex μ r) : Monotone (swapDiagonalStepsFun μ r hr).

**Theorem 1.6 (swapDiagonalStepsFun_injective).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalStepsFun_injective`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalStepsFun_injective` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

`swapDiagonalStepsFun` is injective. Follows from monotonicity + coordinate-sum preservation (same argument as for `insertLeftStep`).

In this notation, lemma swapDiagonalStepsFun_injective {p q : ℕ} (μ : Shuffle (p) (q)) (r : Index (p + (q))) (hr : isDiagonalVertex μ r) : Function.Injective (swapDiagonalStepsFun μ r hr).

**Definition 1.7 (swapDiagonalSteps).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The sign-reversing involution on diagonal terms. Given a `(p, q)`-shuffle `μ` and a diagonal vertex `r`, swap the steps adjacent to `r` (replacing an LR corner with RL or vice versa). This produces a new shuffle `μ'` such that: - `μ' ∘ δ_r = μ ∘ δ_r` (same underlying map after vertex removal) - `μ'.sign = -μ.sign` (opposite sign, from the inversion count change)

In this notation, def swapDiagonalSteps {p q : ℕ} (μ : Shuffle (p) (q)) (r : Index (p + (q))) (hr : isDiagonalVertex μ r) : Shuffle (p) (q).

**Theorem 1.8 (swapDiagonalSteps_apply_ne).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_apply_ne`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_apply_ne` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Every vertex outside the marked corner is preserved.

In this notation, lemma swapDiagonalSteps_apply_ne {p q : ℕ} (μ : Shuffle (p) (q)) (r : Index (p + (q))) (hr : isDiagonalVertex μ r) (i : Index (p + (q))) (hi : i ≠ r) : (swapDiagonalSteps μ r hr).1 i = μ.1 i.

**Theorem 1.9 (swapDiagonalSteps_apply_r_of_left).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_apply_r_of_left`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_apply_r_of_left` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

When the incoming edge is a first-coordinate step, the new corner takes the first coordinate from the preceding vertex and the second from the following vertex.

In this notation, lemma swapDiagonalSteps_apply_r_of_left {p q : ℕ} (μ : Shuffle (p) (q)) (r : Index (p + (q))) (hr : isDiagonalVertex μ r) (hL : isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩) : (swapDiagonalSteps μ r hr).1 r = (⟨(μ.1 r).1.val - 1, by exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt ( μ.1 r |>.1 ) ] )⟩, ⟨(μ.1 r).2.val + 1, by have h_snd_range : (μ.1 r).2.val < q := by have h_snd_lt : (μ.1 r).2.val < q := by have h_not_left : ¬isLeftStep μ ⟨r.val, (isDiagonalVertex_bounds hr).2⟩ := by unfold isDiagonalVertex at hr; simp [hL] at hr; tauto; have h_step := shuffle_step μ ⟨r.val, (isDiagonalVertex_bounds hr).2⟩ generalize_proofs at *; unfold isLeftStep at h_not_left; simp_all +decide [ Fin.castSucc, Fin.succ ] ; omega; generalize_proofs at *; exact h_snd_lt.trans_le ( Nat.le_refl _ ) |> lt_of_lt_of_le <| Nat.le_refl _; linarith [h_snd_range]⟩).

**Theorem 1.10 (swapDiagonalSteps_apply_r_of_right).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_apply_r_of_right`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_apply_r_of_right` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

When the incoming edge is a second-coordinate step, the new corner takes the first coordinate from the following vertex and the second from the preceding vertex.

In this notation, lemma swapDiagonalSteps_apply_r_of_right {p q : ℕ} (μ : Shuffle (p) (q)) (r : Index (p + (q))) (hr : isDiagonalVertex μ r) (hR : ¬ isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩) : (swapDiagonalSteps μ r hr).1 r = (⟨(μ.1 r).1.val + 1, by unfold isDiagonalVertex at hr; simp_all +decide []; split_ifs at hr; simp_all +decide [ isLeftStep ]; grind⟩, ⟨(μ.1 r).2.val - 1, by exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt ( μ.1 r |>.2 ) ] )⟩).

**Theorem 1.11 (swapDiagonalSteps_flip_prev).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_flip_prev`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_flip_prev` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The incoming edge type at the marked vertex is reversed.

In this notation, lemma swapDiagonalSteps_flip_prev {p q : ℕ} (μ : Shuffle p q) (r : Index (p + q)) (hr : isDiagonalVertex μ r) : isLeftStep (swapDiagonalSteps μ r hr) ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩ ↔ ¬ isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩.

**Theorem 1.12 (swapDiagonalSteps_flip_curr).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_flip_curr`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_flip_curr` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The outgoing edge type at the marked vertex is reversed.

In this notation, lemma swapDiagonalSteps_flip_curr {p q : ℕ} (μ : Shuffle p q) (r : Index (p + q)) (hr : isDiagonalVertex μ r) : isLeftStep (swapDiagonalSteps μ r hr) ⟨r.val, by have := (isDiagonalVertex_bounds hr).2; omega⟩ ↔ ¬ isLeftStep μ ⟨r.val, by have := (isDiagonalVertex_bounds hr).2; omega⟩.

**Theorem 1.13 (swapDiagonalSteps_vertex).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_vertex`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_vertex` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The marked vertex is diagonal in the swapped path as well.

In this notation, lemma swapDiagonalSteps_vertex {p q : ℕ} (μ : Shuffle (p) (q)) (r : Index (p + (q))) (hr : isDiagonalVertex μ r) : isDiagonalVertex (swapDiagonalSteps μ r hr) r.

**Theorem 1.14 (swapDiagonalSteps_apply_ne_r).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_apply_ne_r`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_apply_ne_r` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The swapped shuffle agrees with the original shuffle at every index different from the marked index.

In this notation, lemma swapDiagonalSteps_apply_ne_r {p q : ℕ} (μ : Shuffle (p) (q)) (r : Index (p + (q))) (hr : isDiagonalVertex μ r) (i : Index (p + (q))) (h : i ≠ r) : (swapDiagonalSteps μ r hr).1 i = μ.1 i.

**Theorem 1.15 (swapDiagonalSteps_val_r).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_val_r`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_val_r` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The new corner coordinates are obtained by adding the appropriate unit increment to the preceding vertex, as determined by the incoming step type.

In this notation, lemma swapDiagonalSteps_val_r {p q : ℕ} (μ : Shuffle (p) (q)) (r : Index (p + (q))) (hr : isDiagonalVertex μ r) (rm1 : Fin ((p) + (q))) (h_rm1 : rm1.val = r.val - 1) : (swapDiagonalSteps μ r hr).1 r = if h : isLeftStep μ rm1 then (⟨(μ.1 r).1.val - 1, by grind⟩, ⟨(μ.1 r).2.val + 1, by have h_snd_lt : ¬isLeftStep μ ⟨r.val, by have := (isDiagonalVertex_bounds hr).2; omega⟩ := by have h_snd_lt : ¬isLeftStep μ ⟨r.val, by have := (isDiagonalVertex_bounds hr).2; omega⟩ := by have := hr unfold isDiagonalVertex at this have h_snd_lt : isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩ := by convert h using 1 generalize_proofs at *; ( exact Fin.ext ( by aesop );) generalize_proofs at *; ( split_ifs at this; tauto;) (generalize_proofs at *; ( exact h_snd_lt)) generalize_proofs at *; ( have hstep := shuffle_step μ ⟨r.val, by have := (isDiagonalVertex_bounds hr).2; omega⟩ generalize_proofs at *; ( unfold isLeftStep at h_snd_lt; simp_all +decide [ Fin.castSucc, Fin.succ ] ; omega;))⟩) else (⟨(μ.1 r).1.val + 1, by convert Nat.lt_succ_of_le ( Fin.is_le _ ) using 1; on_goal 1 => convert rfl convert Fin.val_cast_of_lt _; · infer_instance; · contrapose! h; unfold isDiagonalVertex at hr; simp_all +decide only [Fin.val_pos_iff, isLeftStep, Fin.castSucc_mk, Fin.succ_mk, Fin.val_fin_lt, Fin.eta, not_lt, dite_false_right, add_le_add_iff_right]; rw [ show rm1.castSucc = ⟨ r.val - 1, by omega ⟩ from ?_, show rm1.succ = r from ?_ ]; · grind; · exact Fin.ext ( by simp +decide [ h_rm1, Nat.sub_add_cancel ( show 1 ≤ ( r : ℕ ) from Nat.pos_of_ne_zero ( by aesop_cat ) ) ] ); · exact Fin.ext h_rm1⟩, ⟨(μ.1 r).2.val - 1, by exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt ( μ.1 r |>.2 ) ] )⟩).

**Theorem 1.16 (swapDiagonalSteps_isLeftStep_toggle).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_isLeftStep_toggle`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_isLeftStep_toggle` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The incoming first-coordinate-step predicate is negated by the corner swap.

In this notation, lemma swapDiagonalSteps_isLeftStep_toggle {p q : ℕ} (μ : Shuffle p q) (r : Index (p + q)) (hr : isDiagonalVertex μ r) : let rm1 : Fin (p + q) := ⟨r.val - 1, by unfold isDiagonalVertex at hr; split_ifs at hr; omega⟩; isLeftStep (swapDiagonalSteps μ r hr) rm1 ↔ ¬ isLeftStep μ rm1.

**Theorem 1.17 (swapDiagonalSteps_involutive).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_involutive` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Swapping the two steps around the same marked diagonal vertex twice recovers the original path.

In this notation, lemma swapDiagonalSteps_involutive {p q : ℕ} (μ : Shuffle (p) (q)) (r : Index (p + (q))) (hr : isDiagonalVertex μ r) : swapDiagonalSteps (swapDiagonalSteps μ r hr) r (swapDiagonalSteps_vertex μ r hr) = μ.

**Theorem 1.18 (swapDiagonalSteps_neg_sign).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_neg_sign`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_neg_sign` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The swap negates the signed coefficient. Derives from `swapDiagonalSteps_invCount_sum_odd`: since the invCount sum is odd, `(-1)^invCount' * (-1)^invCount = -1`, and multiplying both sides by `(-1)^invCount` (which squares to 1) gives `(-1)^invCount' = -(-1)^invCount`.

In this notation, @[grind =] lemma swapDiagonalSteps_neg_sign {p q : ℕ} (μ : Shuffle (p) (q)) (r : Index (p + (q))) (hr : isDiagonalVertex μ r) : (swapDiagonalSteps μ r hr).sign = -(μ.sign).

**Theorem 1.19 (swapDiagonalSteps_ne).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_ne`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_ne` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The swap involution is never the identity: swapping two steps of different type always produces a distinct shuffle.

In this notation, lemma swapDiagonalSteps_ne {p q : ℕ} (μ : Shuffle (p) (q)) (r : Index (p + (q))) (hr : isDiagonalVertex μ r) : swapDiagonalSteps μ r hr ≠ μ.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.diagonal_left_fst_pos`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.diagonal_right_snd_pos`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.isDiagonalVertex_bounds`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalStepsFun`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalStepsFun_injective`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalStepsFun_monotone`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_apply_ne`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_apply_ne_r`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_apply_r_of_left`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_apply_r_of_right`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_flip_curr`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_flip_prev`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_involutive`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_isLeftStep_toggle`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_ne`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_neg_sign`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_val_r`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal.swapDiagonalSteps_vertex`
- Dependency: [D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval](ShuffleRemoval.md)
