/- GID: D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sign-reversing involution cancelling diagonal shuffle faces. -/

/-
Copyright (c) 2026 Jeffrey Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey Li

Source: LeanPool/EilenbergZilber, revision 8bbde3a6de815108d41922c9362ebbe38422663a.
Original source: jeffrey-dot-li/lean-homology, revision
40c5aae235b0f499ebfc1e68ce574a62b531203c; author release
fd0147a1ffe4f3c14c247574e148893d7cdf8cf6 (LeanPool PR 588).
Modifications: receiving namespace and imports, module boundaries, exposure of
consumed private interfaces, canonical identifier spellings, and omission of unused
companion, reflexive binding, and frontal material.
-/

module

public import D5.S3.HomologicalAlgebra.EilenbergZilber.ShuffleRemoval

@[expose] public section

noncomputable section

namespace D5.S3.HomologicalAlgebra.EilenbergZilber

namespace Shuffle

/-- Extract the two facts from `isDiagonalVertex`: `0 < r` and `r < p+q`. -/
lemma isDiagonalVertex_bounds {p q : ℕ} {μ : Shuffle p q}
    {r : Index (p + (q))} (hr : isDiagonalVertex μ r) :
    0 < r.val ∧ r.val < (p) + (q) := by
  unfold isDiagonalVertex at hr
  split_ifs at hr with h₁ h₂
  exact ⟨‹_›, ‹_›⟩

/-- At a diagonal vertex with a left step at `r-1`, the shuffle step from
`r-1` to `r` increments fst, giving `μ(r).1 ≥ 1`. -/
lemma diagonal_left_fst_pos {p q : ℕ} {μ : Shuffle (p) (q)}
    {r : Index (p + (q))} (hr : isDiagonalVertex μ r)
    (hL : isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩) :
    0 < (μ.1 r).1.val := by
  have ⟨h₁, h₂⟩ := isDiagonalVertex_bounds hr
  have hstep := shuffle_step μ ⟨r.val - 1, by omega⟩
  have hcs : (⟨r.val - 1, by omega⟩ : Fin ((p) + (q))).castSucc =
      (⟨r.val - 1, by omega⟩ : Index ((p) + (q))) :=
    Fin.ext (by simp [Fin.castSucc])
  have hsu : (⟨r.val - 1, by omega⟩ : Fin ((p) + (q))).succ = r :=
    Fin.ext (by simp [Fin.succ]; omega)
  rw [hcs, hsu] at hstep
  unfold isLeftStep at hL; rw [hcs, hsu] at hL
  rcases hstep with ⟨h1, _⟩ | ⟨h1, _⟩
  · omega
  · omega

/-- At a diagonal vertex with a right step at `r-1`, the shuffle step from
`r-1` to `r` increments snd, giving `μ(r).2 ≥ 1`. -/
lemma diagonal_right_snd_pos {p q : ℕ} {μ : Shuffle (p) (q)}
    {r : Index (p + (q))} (hr : isDiagonalVertex μ r)
    (hR : ¬isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩) :
    0 < (μ.1 r).2.val := by
  have ⟨h₁, h₂⟩ := isDiagonalVertex_bounds hr
  have hstep := shuffle_step μ ⟨r.val - 1, by omega⟩
  have hcs : (⟨r.val - 1, by omega⟩ : Fin ((p) + (q))).castSucc =
      (⟨r.val - 1, by omega⟩ : Index ((p) + (q))) :=
    Fin.ext (by simp [Fin.castSucc])
  have hsu : (⟨r.val - 1, by omega⟩ : Fin ((p) + (q))).succ = r :=
    Fin.ext (by simp [Fin.succ]; omega)
  rw [hcs, hsu] at hstep
  unfold isLeftStep at hR; rw [hcs, hsu] at hR
  rcases hstep with ⟨h1, _⟩ | ⟨_, h2⟩
  · omega
  · omega

/-- The underlying function for `swapDiagonalSteps`: agrees with `μ` everywhere
except at vertex `r`, where the step type is swapped.
- LR diagonal (left then right): `μ(r)` becomes `(μ(r).1 - 1, μ(r).2 + 1)`
- RL diagonal (right then left): `μ(r)` becomes `(μ(r).1 + 1, μ(r).2 - 1)` -/
def swapDiagonalStepsFun {p q : ℕ} (μ : Shuffle p q)
    (r : Index (p + (q))) (hr : isDiagonalVertex μ r) :
    Index ((p ) + (q )) → Index (p) × Index (q) :=
  fun i =>
    if i = r then
      have ⟨h₁, h₂⟩ := isDiagonalVertex_bounds hr
      have hsum := coordSum_eq μ r
      if hL : isLeftStep μ ⟨r.val - 1, by omega⟩ then
        -- LR case: fst decrements, snd increments
        -- fst ≥ 1 (step r-1 incremented fst) so fst - 1 is valid
        have hfst_pos := diagonal_left_fst_pos hr hL
        -- snd < q+1 because step r is right (snd increments at r),
        -- so μ(r+1).2 > μ(r).2 and μ(r+1).2 ≤ q+1
        have hsnd_lt : (μ.1 r).2.val < q := by
          -- Step r is right (not left) in LR diagonal, so snd increments at r
          unfold isDiagonalVertex at hr; simp [h₁, h₂] at hr
          have hnotL : ¬isLeftStep μ ⟨r.val, h₂⟩ := by tauto
          have hstep := shuffle_step μ ⟨r.val, h₂⟩
          have hcs : (⟨r.val, h₂⟩ : Fin ((p) + (q))).castSucc = r :=
            Fin.ext (by simp [Fin.castSucc])
          rw [hcs] at hstep
          unfold isLeftStep at hnotL; rw [hcs] at hnotL
          have hsucc_snd := (μ.1 (⟨r.val, h₂⟩ : Fin ((p) + (q))).succ).2.isLt
          rcases hstep with ⟨h1, _⟩ | ⟨_, h2⟩
          · exfalso; exact hnotL (by omega)
          · omega
        (⟨(μ.1 r).1.val - 1, by omega⟩,
         ⟨(μ.1 r).2.val + 1, by omega⟩)
      else
        -- RL case: fst increments, snd decrements
        -- snd ≥ 1 (step r-1 incremented snd) so snd - 1 is valid
        have hsnd_pos := diagonal_right_snd_pos hr (by exact hL)
        -- fst < p+1 because step r is left (fst increments at r),
        -- so μ(r+1).1 > μ(r).1 and μ(r+1).1 ≤ p+1
        have hfst_lt : (μ.1 r).1.val < p := by
          -- Step r is left in RL diagonal, so fst increments at r
          unfold isDiagonalVertex at hr; simp [h₁, h₂] at hr
          have hisL : isLeftStep μ ⟨r.val, h₂⟩ := by tauto
          have hstep := shuffle_step μ ⟨r.val, h₂⟩
          have hcs : (⟨r.val, h₂⟩ : Fin ((p) + (q))).castSucc = r :=
            Fin.ext (by simp [Fin.castSucc])
          rw [hcs] at hstep
          unfold isLeftStep at hisL; rw [hcs] at hisL
          have hsucc_fst := (μ.1 (⟨r.val, h₂⟩ : Fin ((p) + (q))).succ).1.isLt
          rcases hstep with ⟨h1, _⟩ | ⟨h1, _⟩
          · omega
          · exfalso; exact absurd (by omega : (μ.1 r).1.val < _) (by omega)
        (⟨(μ.1 r).1.val + 1, by omega⟩,
         ⟨(μ.1 r).2.val - 1, by omega⟩)
    else
      μ.1 i

/-- `swapDiagonalStepsFun` preserves the coordinate sum: fst + snd = i for all i.
At `i ≠ r` this is `coordSum_eq μ`. At `i = r` the ±1 adjustments cancel. -/
private lemma swapDiagonalStepsFun_coordSum {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) (i : Index ((p) + (q))) :
    (swapDiagonalStepsFun μ r hr i).1.val +
      (swapDiagonalStepsFun μ r hr i).2.val = i.val := by
  have hsum := coordSum_eq μ i
  unfold swapDiagonalStepsFun
  split_ifs with hi
  · subst hi
    split
    dsimp only
    split_ifs with hL
    · have := diagonal_left_fst_pos hr hL
      dsimp only
      omega
    · have := diagonal_right_snd_pos hr hL
      dsimp only
      omega
  · exact hsum

/- `swapDiagonalStepsFun` is monotone in the product order. Only the pairs
`(r-1, r)` and `(r, r+1)` need checking — the two adjacent steps swap type
(LR↔RL) but both remain valid (one coordinate +1, the other unchanged). -/
section

private lemma swapDiagonalStepsFun_local_bounds {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) :
    μ.1 ⟨r.val - 1, by have := isDiagonalVertex_bounds hr; omega⟩ ≤ swapDiagonalStepsFun μ r hr r ∧
    swapDiagonalStepsFun μ r hr r ≤ μ.1 ⟨r.val + 1, by have := isDiagonalVertex_bounds hr;
                                                         omega⟩ := by
      -- By definition of swapDiagonalStepsFun, we need to consider the two cases for the diagonal
      -- vertex.
      by_cases hL : isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩
      all_goals generalize_proofs at *;
      · -- By definition of swapDiagonalStepsFun, when isLeftStep is true, the function returns
        -- (μ(r-1).fst, μ(r-1).snd + 1).
        have h_swap : μ.swapDiagonalStepsFun r hr r = (⟨(μ.1 r).1.val - 1, by
          exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt ( μ.1 r |>.1 ) ]
                                                                )⟩, ⟨(μ.1 r).2.val + 1, by
          simp +zetaDelta only [Order.lt_add_one_iff, tsub_le_iff_right, Fin.is_le',
              Order.add_one_le_iff] at *;
          unfold isDiagonalVertex at hr
          generalize_proofs at *;
          have hnotL : ¬isLeftStep μ ⟨r.val, by
            assumption⟩ := by
            grind +ring
          generalize_proofs at *;
          have hstep := shuffle_step μ ⟨r.val, by
            assumption⟩
          generalize_proofs at *;
          unfold isLeftStep at hnotL; simp_all +decide [ Fin.castSucc, Fin.succ ] ; omega;⟩) := by
          unfold D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.swapDiagonalStepsFun; aesop;
        generalize_proofs at *;
        -- By definition of swapDiagonalStepsFun, we know that μ(r) is equal to (μ(r-1).fst + 1,
        -- μ(r-1).snd).
        have h_mu_r : μ.1 r = (⟨(μ.1 ⟨r.val - 1, by
          omega⟩).1.val + 1, by
          exact Nat.lt_succ_of_le ( Nat.le_trans ( Nat.succ_le_of_lt hL ) ( Nat.le_of_lt_succ (
              by simp only [Fin.succ_mk,
            Nat.succ_eq_add_one, Fin.is_lt] ) ) ) ⟩,
            ⟨(μ.1 ⟨r.val - 1, by
          omega⟩).2.val, by
          grind only []⟩) := by
          all_goals generalize_proofs at *;
          have h_step : μ.1 (Fin.succ ⟨r.val - 1, by
            omega⟩) = (⟨(μ.1 ⟨r.val - 1, by
            omega⟩).1.val + 1, by
            omega⟩, ⟨(μ.1 ⟨r.val - 1, by
            omega⟩).2.val, by
            linarith⟩) := by
            have := shuffle_step μ ⟨r.val - 1, by
              omega⟩
            generalize_proofs at *;
            rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all +decide [ isLeftStep ] ; omega
          generalize_proofs at *;
          convert h_step using 1
          generalize_proofs at *; (
          congr! 1
          generalize_proofs at *; (
          exact Eq.symm ( Fin.ext <| Nat.succ_pred_eq_of_pos <| Nat.pos_of_ne_zero <|
              by rintro h; have := isDiagonalVertex_bounds hr; aesop )))
        generalize_proofs at *;
        have h_mu_r_next : μ.1 ⟨r.val + 1, by
          omega⟩ = (⟨(μ.1 r).1.val, by
          exact (μ.1 r).1.isLt⟩, ⟨(μ.1 r).2.val + 1, by
          omega⟩) := by
          have h_mu_r_next : ¬isLeftStep μ ⟨r.val, by
            exact Nat.lt_of_succ_lt_succ ‹_›⟩ := by
            unfold isDiagonalVertex at hr; simp +decide [ hL ] at hr; tauto;
          generalize_proofs at *;
          have := shuffle_step μ ⟨r.val, by
            linarith [ Fin.is_lt r ]⟩
          generalize_proofs at *;
          simp_all +decide only [isLeftStep, Fin.castSucc_mk, Fin.succ_mk, Fin.val_fin_lt, Fin.eta,
              add_tsub_cancel_right, not_lt];
          ext <;> simp_all +decide [ Fin.ext_iff, Prod.ext_iff ] <;> omega
        generalize_proofs at *;
        simp_all +decide [ Prod.le_def, Fin.le_def ];
      · -- Since μ(r-1) is a right step, we have (μ.1 r).2 = (μ.1 r-1).2 + 1.
        have h_right_step : (μ.1 r).2.val = (μ.1 ⟨r.val - 1, by
          omega⟩).2.val + 1 := by
          have h_right_step : (μ.1 ⟨r.val - 1, by
            omega⟩).1.val = (μ.1 r).1.val := by
            rcases r with ⟨ _ | r, hr ⟩ <;> norm_num at *;
            exact Classical.not_not.1 fun h => hL <| by exact lt_of_le_of_ne ( by exact μ.1.monotone
                                                                                   ( Nat.le_succ _ )
                                                                                   |> And.left
                                                                                   ) <| Ne.symm <|
                                                                                   by aesop;
          generalize_proofs at *;
          have := coordSum_eq μ ⟨r.val - 1, by
            omega⟩
          generalize_proofs at *;
          have := coordSum_eq μ r
          generalize_proofs at *;
          have := coordSum_eq μ ⟨r.val + 1, by
            linarith [ Fin.is_lt r ]⟩
          generalize_proofs at *;
          rcases r with ⟨ _ | r, hr ⟩ <;> simp_all +arith +decide only [Fin.zero_eta, zero_tsub,
              Nat.add_eq_zero_iff, Fin.val_eq_zero_iff, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
              add_zero, zero_add, zero_ne_one, add_tsub_cancel_right]
          · generalize_proofs at *
            unfold isDiagonalVertex at hr; simp_all +decide ;
          · linarith! [ shuffle_step μ ⟨ r, by linarith ⟩ ]
        generalize_proofs at *;
        have h_left_step : (μ.1 ⟨r.val + 1, by
          grind only []⟩).1.val = (μ.1 r).1.val + 1 := by
          have := shuffle_step μ ⟨ r.val, by
            linarith [ Fin.is_lt r ] ⟩
          generalize_proofs at *;
          unfold isDiagonalVertex at hr; simp_all +decide [ isLeftStep ] ; omega;
        generalize_proofs at *;
        -- By definition of `swapDiagonalStepsFun`, we need to consider the two cases for the
        -- diagonal vertex. Since `hL` is false, we have `¬isLeftStep μ ⟨r.val - 1, _⟩`.
        have h_swap : swapDiagonalStepsFun μ r hr r = (⟨(μ.1 r).1.val + 1, by
          grind only []⟩, ⟨(μ.1 r).2.val - 1, by
          grind only []⟩) := by
          -- By definition of swapDiagonalStepsFun, when i = r and hL is false, we have:
          simp [swapDiagonalStepsFun, hL]
        generalize_proofs at *;
        constructor <;> simp_all +decide only [add_tsub_cancel_right, Fin.eta, Prod.le_def,
            Std.le_refl, and_true];
        · exact Nat.le_succ_of_le ( μ.1.monotone ( Nat.pred_le _ ) |> And.left );
        · constructor
          · simp only [Fin.le_iff_val_le_val]; omega
          -- `by omega` alone fails: omega doesn't reduce `Fin.le` to `val ≤ val`,
          -- so we `simp [Fin.le_def]` first to expose the ℕ comparison.
          · exact μ.1.monotone (show _ ≤ _ by simp [Fin.le_def]; omega) |>.2

end

lemma swapDiagonalStepsFun_monotone {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) :
    Monotone (swapDiagonalStepsFun μ r hr) := by
  -- Let's unfold the definition of `swapDiagonalStepsFun`.
  unfold swapDiagonalStepsFun;
  intro i j hij; by_cases hi : i = r <;> by_cases hj : j = r <;> simp +decide only [hi, hj,
      Std.le_refl, ↓reduceIte] at hij ⊢;
  · have h_swap_diag : swapDiagonalStepsFun μ r hr r ≤ μ.1 j := by
      have h_swap_diag : swapDiagonalStepsFun μ r hr r ≤ μ.1 ⟨r.val + 1, by
        grind⟩ := by
        exact swapDiagonalStepsFun_local_bounds μ r hr |>.2
      generalize_proofs at *;
      refine le_trans h_swap_diag ?_
      exact μ.1.monotone ( Nat.succ_le_of_lt ( hij.lt_of_ne' hj ) );
    unfold swapDiagonalStepsFun at h_swap_diag; simp_all +decide [ Fin.ext_iff ] ;
  · have := swapDiagonalStepsFun_local_bounds μ r hr;
    convert this.1.trans' _ using 1;
    · unfold D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.swapDiagonalStepsFun; aesop;
    · exact μ.1.monotone ( Nat.le_pred_of_lt ( hij.lt_of_ne hi ) );
  · exact μ.1.monotone hij

/-- `swapDiagonalStepsFun` is injective.  Follows from monotonicity +
coordinate-sum preservation (same argument as for `insertLeftStep`). -/
lemma swapDiagonalStepsFun_injective {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) :
    Function.Injective (swapDiagonalStepsFun μ r hr) := by
  intro i j hij
  apply Fin.ext
  calc i.val = (swapDiagonalStepsFun μ r hr i).1.val +
      (swapDiagonalStepsFun μ r hr i).2.val :=
        (swapDiagonalStepsFun_coordSum μ r hr i).symm
    _ = (swapDiagonalStepsFun μ r hr j).1.val +
      (swapDiagonalStepsFun μ r hr j).2.val := congrArg (fun x => x.1.val + x.2.val) hij
    _ = j.val := swapDiagonalStepsFun_coordSum μ r hr j


/-- The sign-reversing involution on diagonal terms.  Given a `(p, q)`-shuffle
`μ` and a diagonal vertex `r`, swap the steps adjacent to `r` (replacing an LR
corner with RL or vice versa).  This produces a new shuffle `μ'` such that:
- `μ' ∘ δ_r = μ ∘ δ_r` (same underlying map after vertex removal)
- `μ'.sign = -μ.sign` (opposite sign, from the inversion count change) -/
def swapDiagonalSteps {p q : ℕ} (μ : Shuffle (p) (q))
    (r : Index (p + (q))) (hr : isDiagonalVertex μ r) :
    Shuffle (p) (q) :=
  ⟨⟨swapDiagonalStepsFun μ r hr, swapDiagonalStepsFun_monotone μ r hr⟩,
   swapDiagonalStepsFun_injective μ r hr⟩

/- The swap involution preserves the diagonal vertex property. -/
section

/-
For any index `i` different from the diagonal vertex `r`, the shuffle map `swapDiagonalSteps` has
the same value as the original shuffle `μ`. This follows directly from the definition of
`swapDiagonalStepsFun`, which uses an `if i = r` condition.
-/
lemma swapDiagonalSteps_apply_ne {p q : ℕ} (μ : Shuffle (p) (q))
    (r : Index (p + (q))) (hr : isDiagonalVertex μ r)
    (i : Index (p + (q))) (hi : i ≠ r) :
    (swapDiagonalSteps μ r hr).1 i = μ.1 i := by
  exact ite_eq_right hi

/-
If the step entering the diagonal vertex `r` is a Left step, then `swapDiagonalSteps` modifies the
value at `r` by decrementing the first coordinate and incrementing the second. This corresponds to
the `then` branch of `swapDiagonalStepsFun`.
-/
lemma swapDiagonalSteps_apply_r_of_left {p q : ℕ} (μ : Shuffle (p) (q))
    (r : Index (p + (q))) (hr : isDiagonalVertex μ r)
    (hL : isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩) :
    (swapDiagonalSteps μ r hr).1 r =
      (⟨(μ.1 r).1.val - 1, by
        exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt ( μ.1 r |>.1 ) ]
                                                              )⟩, ⟨(μ.1 r).2.val + 1, by
        -- Since the second component of `μ r` is in `Fin (q)`, its value is between 0 and q.
        have h_snd_range : (μ.1 r).2.val < q := by
          have h_snd_lt : (μ.1 r).2.val < q := by
            have h_not_left : ¬isLeftStep μ ⟨r.val, (isDiagonalVertex_bounds hr).2⟩ := by
              unfold isDiagonalVertex at hr; simp [hL] at hr; tauto;
            have h_step := shuffle_step μ ⟨r.val, (isDiagonalVertex_bounds hr).2⟩
            generalize_proofs at *;
            unfold isLeftStep at h_not_left; simp_all +decide [ Fin.castSucc, Fin.succ ] ; omega;
          generalize_proofs at *;
          exact h_snd_lt.trans_le ( Nat.le_refl _ ) |> lt_of_lt_of_le <| Nat.le_refl _;
        linarith [h_snd_range]⟩) := by
        exact ite_eq_left rfl |> fun h => h.trans ( by aesop )

/-
If the step entering the diagonal vertex `r` is a Right step (not
    Left), then `swapDiagonalSteps` modifies the value at `r`
    by incrementing the first coordinate and decrementing the second. This corresponds to the `else`
    branch of `swapDiagonalStepsFun`.
-/
lemma swapDiagonalSteps_apply_r_of_right {p q : ℕ} (μ : Shuffle (p) (q))
    (r : Index (p + (q))) (hr : isDiagonalVertex μ r)
    (hR : ¬ isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩) :
    (swapDiagonalSteps μ r hr).1 r =
      (⟨(μ.1 r).1.val + 1, by
        -- By definition of `isDiagonalVertex`, we know that `isLeftStep μ ⟨r.val, h₂⟩` is false.
        unfold isDiagonalVertex at hr; simp_all +decide [];
        split_ifs at hr; simp_all +decide [ isLeftStep ];
        grind⟩, ⟨(μ.1 r).2.val - 1, by
        exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt ( μ.1 r |>.2 ) ]
                                                              )⟩) := by
        unfold D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.swapDiagonalSteps
        generalize_proofs at *;
        unfold D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.swapDiagonalStepsFun; aesop;

/-
The step entering the diagonal vertex `r` (index `r-1`) flips its type (Left ↔
    Right) under `swapDiagonalSteps`.
Proof sketch:
1. Let `i = r-1`. We compare `(μ'.1 i).1` and `(μ'.1 (i+1)).1`.
2. `μ'.1 i = μ.1 i` since `i ≠ r` (as `r > 0`).
3. `μ'.1 (i+1) = μ'.1 r`.
4. If `isLeftStep μ i` is true (Left step):
   - `(μ.1 i).1 + 1 = (μ.1 r).1`.
   - `(μ'.1 r).1 = (μ.1 r).1 - 1` (by `swapDiagonalSteps_apply_r_of_left`).
   - So `(μ'.1 r).1 = (μ.1 i).1`.
   - Thus `isLeftStep μ' i` is false.
5. If `isLeftStep μ i` is false (Right step):
   - `(μ.1 i).1 = (μ.1 r).1`.
   - `(μ'.1 r).1 = (μ.1 r).1 + 1` (by `swapDiagonalSteps_apply_r_of_right`).
   - So `(μ'.1 i).1 < (μ'.1 r).1`.
   - Thus `isLeftStep μ' i` is true.
-/
lemma swapDiagonalSteps_flip_prev {p q : ℕ} (μ : Shuffle (p) (q))
    (r : Index (p + (q))) (hr : isDiagonalVertex μ r) :
    isLeftStep (swapDiagonalSteps μ r hr) ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2;
                                                          omega⟩ ↔
    ¬ isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2; omega⟩ := by
      unfold isLeftStep
      generalize_proofs at *;
      by_cases hL : isLeftStep μ ⟨ r.val - 1, by have := ( isDiagonalVertex_bounds hr ).2; omega
                                                  ⟩ <;> simp_all +decide only [Fin.castSucc_mk,
                                                  Fin.succ_mk, Fin.val_fin_lt, not_lt];
      · rcases r with ⟨ _ | r, hr ⟩ <;> simp_all +decide only [isLeftStep, zero_tsub,
            Fin.castSucc_mk, Fin.zero_eta, Fin.succ_mk, zero_add, Fin.val_fin_lt,
            add_tsub_cancel_right];
        · unfold isDiagonalVertex at hr
          simp at hr
        · rw [ swapDiagonalSteps_apply_r_of_left ] <;> norm_num [ hL ];
          · constructor <;> intro h <;> contrapose! h;
            · convert Nat.le_refl _ using 1;
              rotate_left;
              · exact ( μ.1 ⟨ r + 1, by omega ⟩ |>.1 : ℕ ) - 1
              (generalize_proofs at *; (simp_all +decide only [add_tsub_cancel_right, Fin.le_def,
                  tsub_le_iff_right, Std.le_refl, iff_true] ););
              rw [ swapDiagonalSteps_apply_ne ] <;> norm_num [ h ];
              have := shuffle_step μ ⟨ r, by omega ⟩; aesop;
            · exact hL
          · exact hL;
      · rcases r with ⟨ _ | r, hr ⟩ <;> simp_all +decide only [zero_tsub, Fin.zero_eta, zero_add,
            add_tsub_cancel_right];
        · unfold isDiagonalVertex at hr;
          grind +ring;
        · -- Since `hL` states that `isLeftStep μ ⟨r, by omega⟩` is false, we have `(μ.1 ⟨r, by
          -- omega⟩).1 = (μ.1 ⟨r + 1, by omega⟩).1`.
          have h_eq : (μ.1 ⟨r, by omega⟩).1 = (μ.1 ⟨r + 1, by omega⟩).1 := by
            -- Since `hL` states that `isLeftStep μ ⟨r, by omega⟩` is false, we have `(μ.1 ⟨r, by
            -- omega⟩).1 = (μ.1 ⟨r + 1, by omega⟩).1` by definition of `isLeftStep`.
            simp only [isLeftStep, Fin.castSucc_mk, Fin.succ_mk, Fin.val_fin_lt, not_lt] at hL ⊢
            generalize_proofs at *; (
            exact le_antisymm ( by simpa using μ.1.monotone ( show ⟨ r, by omega ⟩ ≤ ⟨ r + 1,
                                    by omega ⟩ from Nat.le_succ _ ) |> And.left ) hL)
          generalize_proofs at *; (
          rw [ swapDiagonalSteps_apply_ne, swapDiagonalSteps_apply_r_of_right
              ] <;> simp_all +decide only [add_tsub_cancel_right, Std.le_refl, iff_true, gt_iff_lt,
              not_false_eq_true, ne_eq, Fin.mk.injEq, Nat.left_eq_add];
          exact Nat.lt_succ_self _)

/-
The step leaving the diagonal vertex `r` (index `r`) flips its type (Left ↔
    Right) under `swapDiagonalSteps`.
Proof sketch:
1. Let `i = r`. We compare `isLeftStep μ' i` with `isLeftStep μ i`.
2. `μ'.1 (i+1) = μ.1 (i+1)` since `i+1 ≠ r`.
3. `μ'.1 i` is given by `swapDiagonalSteps_apply_r_of_left` or `_right`.
4. If `isLeftStep μ (r-1)` is true (Left incoming):
   - `μ` has Left at `r-1`. Since `r` is diagonal, `μ` must have Right at `r`.
   - So `isLeftStep μ r` is false.
   - We want to show `isLeftStep μ' r` is true.
   - `μ'.1 r = (μ.1 r).1 - 1`.
   - `μ.1 (r+1) = (μ.1 r).1` (since step `r` is Right).
   - So `(μ'.1 r).1 < (μ'.1 (r+1)).1` becomes `(μ.1 r).1 - 1 < (μ.1 r).1`, which is true.
5. If `isLeftStep μ (r-1)` is false (Right incoming):
   - `μ` has Right at `r-1`. Since `r` is diagonal, `μ` must have Left at `r`.
   - So `isLeftStep μ r` is true.
   - We want to show `isLeftStep μ' r` is false.
   - `μ'.1 r = (μ.1 r).1 + 1`.
   - `μ.1 (r+1) = (μ.1 r).1 + 1` (since step `r` is Left).
   - So `(μ'.1 r).1 < (μ'.1 (r+1)).1` becomes `(μ.1 r).1 + 1 < (μ.1 r).1 + 1`, which is false.
-/
lemma swapDiagonalSteps_flip_curr {p q : ℕ} (μ : Shuffle (p) (q))
    (r : Index (p + (q))) (hr : isDiagonalVertex μ r) :
    isLeftStep (swapDiagonalSteps μ r hr) ⟨r.val, by have := (isDiagonalVertex_bounds hr).2;
                                                      omega⟩ ↔
    ¬ isLeftStep μ ⟨r.val, by have := (isDiagonalVertex_bounds hr).2; omega⟩ := by
      unfold D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.isLeftStep
      generalize_proofs at *;
      by_cases h : isLeftStep μ ⟨r.val - 1, by
        exact lt_of_le_of_lt ( Nat.pred_le _ ) ‹_›⟩
      all_goals generalize_proofs at *;
      · have h_step : (μ.1 (Fin.succ ⟨r.val, by
          assumption⟩)).1.val = (μ.1 ⟨r.val, by
          grind only []⟩).1.val := by
          have := shuffle_step μ ⟨r.val, by
            assumption⟩
          generalize_proofs at *;
          unfold isDiagonalVertex at hr; simp_all +decide [] ;
          unfold Shuffle.isLeftStep at hr; simp_all +decide [] ;
          grind only []
        generalize_proofs at *;
        have := swapDiagonalSteps_apply_r_of_left μ r hr h; simp_all +decide only [Fin.succ,
            Fin.eta, Fin.castSucc, Fin.castAdd_mk, lt_self_iff_false, not_false_eq_true, iff_true,
            gt_iff_lt];
        convert Nat.sub_lt ( diagonal_left_fst_pos hr h ) zero_lt_one using 1
        generalize_proofs at *;
        convert h_step using 1
        generalize_proofs at *; (
        exact congr_arg Fin.val ( swapDiagonalSteps_apply_ne μ r hr ⟨ r.val + 1,
            by omega ⟩ ( by simp +decide [ Fin.ext_iff ] ) |> congr_arg Prod.fst
            ) |> Eq.trans <| rfl);
      · simp_all +decide only [Fin.castSucc, Fin.castAdd_mk, Fin.eta, Fin.succ, Fin.val_fin_lt,
            not_lt];
        rw [ show ( μ.swapDiagonalSteps r hr : D5.S3.HomologicalAlgebra.EilenbergZilber.Index ( p + ( q ) ) →o
            D5.S3.HomologicalAlgebra.EilenbergZilber.Index ( p ) × D5.S3.HomologicalAlgebra.EilenbergZilber.Index ( q ) ) r =
            ( ⟨ ( μ.1 r ).1.val + 1, by
              unfold D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.isDiagonalVertex at hr; simp_all +decide [] ;
              have := μ.1 r |>.1.isLt; have := μ.1 r |>.2.isLt;
                  simp_all +arith +decide [ D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.isLeftStep ];
              grind only [] ⟩, ⟨ ( μ.1 r ).2.val - 1, by
              exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt ( μ.1 r |>.2
                                                                    ) ] ) ⟩ ) from ?_ ]
        all_goals generalize_proofs at *;
        · rw [ show ( μ.swapDiagonalSteps r hr : D5.S3.HomologicalAlgebra.EilenbergZilber.Index ( p + ( q ) ) →o
              D5.S3.HomologicalAlgebra.EilenbergZilber.Index ( p ) × D5.S3.HomologicalAlgebra.EilenbergZilber.Index ( q ) ) ⟨ r.val
              + 1, by omega ⟩ = μ.1 ⟨ r.val + 1, by omega ⟩ from ?_ ];
          · rw [ Fin.lt_def, Fin.le_iff_val_le_val ]; simp +arith +decide only [Fin.val_fin_le];
            constructor <;> intro <;> simp_all +decide only [Order.lt_add_one_iff,
                Order.add_one_le_iff, tsub_le_iff_right, Fin.is_le', Nat.succ_le_iff];
            · unfold isDiagonalVertex at hr; simp_all +decide [] ;
              exact le_of_not_gt fun h => h.not_ge <| by have := shuffle_step μ ⟨ r,
                                                          by omega ⟩; unfold isLeftStep at hr;
                                                          aesop;
            · unfold isDiagonalVertex at hr; simp_all +decide only [Fin.val_pos_iff, ↓reduceDIte,
                  false_and, not_false_eq_true, true_and, false_or, dite_eq_ite, ite_false_right];
              exact absurd ‹_› ( not_le_of_gt hr.2 );
          · exact swapDiagonalSteps_apply_ne _ _ _ _ ( ne_of_gt ( Nat.lt_succ_self _ ) );
        · exact swapDiagonalSteps_apply_r_of_right μ r hr h

end

lemma swapDiagonalSteps_vertex {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) :
    isDiagonalVertex (swapDiagonalSteps μ r hr) r := by
  unfold isDiagonalVertex at *; simp_all +decide only [Fin.val_pos_iff, isLeftStep, Fin.castSucc_mk,
      Fin.succ_mk, Fin.val_fin_lt, Fin.eta, not_lt, dite_false_right];
  split_ifs at hr; simp_all +decide only [isLeftStep, Fin.castSucc_mk, Fin.succ_mk, Fin.val_fin_lt,
      Fin.eta, not_lt, exists_true_left];
  -- Apply the lemmas swapDiagonalSteps_flip_prev and swapDiagonalSteps_flip_curr to show that the
  -- step types are different.
  have h_diff : ¬isLeftStep (swapDiagonalSteps μ r ‹_›) ⟨r.val - 1,
      by have := (isDiagonalVertex_bounds ‹_›).2; omega⟩ ∧ isLeftStep (swapDiagonalSteps μ r
      ‹_›) ⟨r.val, by have := (isDiagonalVertex_bounds ‹_›).2;
                       omega⟩ ∨ isLeftStep (swapDiagonalSteps μ r ‹_›) ⟨r.val - 1,
                       by have := (isDiagonalVertex_bounds ‹_›).2;
                           omega⟩ ∧ ¬isLeftStep (swapDiagonalSteps μ r ‹_›) ⟨r.val,
                           by have := (isDiagonalVertex_bounds ‹_›).2; omega⟩ := by
    have := swapDiagonalSteps_flip_prev μ r ‹_›; have := swapDiagonalSteps_flip_curr μ r ‹_›;
        simp_all +decide [ isLeftStep ];
  generalize_proofs at *; (
  cases h_diff <;> simp_all +decide [ isLeftStep ])


/- The swap is an involution. -/
section

/-
The `swapDiagonalSteps` map agrees with the original shuffle at all indices other than `r`.
-/
lemma swapDiagonalSteps_apply_ne_r {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) (i : Index (p + (q))) (h : i ≠ r) :
    (swapDiagonalSteps μ r hr).1 i = μ.1 i := by
  exact ite_eq_right h

/-
The value of the swapped shuffle at the diagonal vertex `r` is given
    by decrementing/incrementing coordinates based on the step type.
-/
lemma swapDiagonalSteps_val_r {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r)
    (rm1 : Fin ((p) + (q)))
    (h_rm1 : rm1.val = r.val - 1) :
    (swapDiagonalSteps μ r hr).1 r =
      if h : isLeftStep μ rm1 then
        (⟨(μ.1 r).1.val - 1, by
          grind⟩, ⟨(μ.1 r).2.val + 1, by
          have h_snd_lt : ¬isLeftStep μ ⟨r.val, by have := (isDiagonalVertex_bounds hr).2;
                                                    omega⟩ := by
            have h_snd_lt : ¬isLeftStep μ ⟨r.val, by have := (isDiagonalVertex_bounds hr).2;
                                                      omega⟩ := by
              have := hr
              unfold isDiagonalVertex at this
              have h_snd_lt : isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2;
                                                           omega⟩ := by
                convert h using 1
                generalize_proofs at *; (
                exact Fin.ext ( by aesop );)
              generalize_proofs at *; (
              split_ifs at this; tauto;)
            (generalize_proofs at *; (
            exact h_snd_lt))
          generalize_proofs at *; (
          have hstep := shuffle_step μ ⟨r.val, by have := (isDiagonalVertex_bounds hr).2; omega⟩
          generalize_proofs at *; (
          unfold isLeftStep at h_snd_lt; simp_all +decide [ Fin.castSucc, Fin.succ ] ; omega;))⟩)
      else
        (⟨(μ.1 r).1.val + 1, by
          convert Nat.lt_succ_of_le ( Fin.is_le _ ) using 1;
          on_goal 1 => convert rfl
          convert Fin.val_cast_of_lt _;
          · infer_instance;
          · contrapose! h;
            unfold isDiagonalVertex at hr; simp_all +decide only [Fin.val_pos_iff, isLeftStep,
                Fin.castSucc_mk, Fin.succ_mk, Fin.val_fin_lt, Fin.eta, not_lt, dite_false_right,
                add_le_add_iff_right];
            rw [ show rm1.castSucc = ⟨ r.val - 1, by omega ⟩ from ?_, show rm1.succ = r from ?_ ];
            · grind;
            · exact Fin.ext ( by simp +decide [ h_rm1, Nat.sub_add_cancel ( show 1 ≤ ( r : ℕ ) from
                                  Nat.pos_of_ne_zero ( by aesop_cat ) ) ] );
            · exact Fin.ext h_rm1⟩, ⟨(μ.1 r).2.val - 1, by
          exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt ( μ.1 r |>.2 ) ]
                                                                )⟩) := by
          -- By definition of swapDiagonalSteps, applying it twice returns the original shuffle.
          simp only [swapDiagonalSteps, OrderHom.coe_mk, swapDiagonalStepsFun, ↓reduceIte] at *; (
          have h_if_eq : (isLeftStep μ ⟨r.val - 1, by have := (isDiagonalVertex_bounds hr).2;
                                                       omega⟩) = (isLeftStep μ rm1) := by
            exact congr_arg _ ( Fin.ext <| by simp +decide [ h_rm1 ] )
          generalize_proofs at *; (
          split_ifs <;> aesop ( simp_config := { singlePass := true } ) ;))

/-
The `swapDiagonalSteps` involution toggles the type (Left/Right) of the step immediately preceding
the diagonal vertex `r`.
-/
lemma swapDiagonalSteps_isLeftStep_toggle {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) :
    let rm1 : Fin ((p) + (q)) := ⟨r.val - 1, by
      unfold isDiagonalVertex at hr
      split_ifs at hr
      omega⟩
    isLeftStep (swapDiagonalSteps μ r hr) rm1 ↔ ¬ isLeftStep μ rm1 := by
      have hrlt: r.val - 1 < p + q := by have := isDiagonalVertex_bounds hr; omega
      have hswap := swapDiagonalSteps_val_r μ r hr ⟨r.val - 1, by exact hrlt⟩ rfl
      generalize_proofs at *;
      split_ifs at hswap <;> simp_all +decide only [isLeftStep, Fin.castSucc_mk, Fin.succ_mk,
          Fin.val_fin_lt, not_lt, Order.lt_add_one_iff, Order.add_one_le_iff, tsub_le_iff_right,
          Fin.is_le'];
      · convert iff_of_false ?_ ?_ using 1
        all_goals generalize_proofs at *;
        · rw [ swapDiagonalSteps_apply_ne_r ] <;> norm_num [ * ];
          · rcases r with ⟨ _ | r, hr ⟩ <;> norm_num at *;
            · simp_all +decide [ Shuffle.apply_zero ];
            · simp_all +decide only [forall_const];
              exact Nat.sub_le_of_le_add <| by linarith! [ show ( μ.1 ⟨ r + 1,
                                                by linarith ⟩ |>.1 : ℕ ) ≤ ( μ.1 ⟨ r,
                                                by linarith ⟩ |>.1 : ℕ ) + 1 from by
                                                            have := shuffle_step μ ⟨ r,
                                                                by linarith ⟩; aesop; ];
          · exact ne_of_lt ( Nat.pred_lt ( ne_bot_of_gt ( isDiagonalVertex_bounds hr |>.1 ) ) );
        · cases r; aesop
      · rw [ swapDiagonalSteps_apply_ne_r μ r hr ⟨ r.val - 1, by omega ⟩ ( by
          rcases r with ⟨ _ | r, hr ⟩ <;> norm_num at *;
          unfold Shuffle.isDiagonalVertex at hr; aesop ( simp_config := { decide := true } ); ) ]
        generalize_proofs at *;
        rcases r with ⟨ _ | r, hr ⟩ <;> simp_all +decide only [zero_tsub, Fin.zero_eta,
            Order.lt_add_one_iff, Order.add_one_le_iff, zero_add, not_false_eq_true, forall_const,
            add_tsub_cancel_right, implies_true];
        · exact absurd (isDiagonalVertex_bounds hr).1 (lt_irrefl _)
        · unfold Shuffle.isLeftStep at *; simp_all +decide only [Fin.castSucc_mk, Fin.succ_mk,
              Fin.val_fin_lt, not_lt, isEmpty_Prop, IsEmpty.forall_iff, iff_true, gt_iff_lt];
          exact Nat.lt_succ_of_le ( by exact le_trans ( by aesop ) ( μ.1.monotone ( Nat.le_succ _ )
                                        |>.1 ) )

end

lemma swapDiagonalSteps_involutive {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) :
    swapDiagonalSteps (swapDiagonalSteps μ r hr) r
      (swapDiagonalSteps_vertex μ r hr) = μ := by
  refine ExistsUnique.unique (p := fun x => x.1 = μ.1) ?_ ?_ ?_
  · use μ; aesop;
  · -- By definition of swapDiagonalSteps, we know that applying it twice returns the original
    -- shuffle.
    have h_swap : ∀ i : Index ((p) + (q)), (swapDiagonalSteps (swapDiagonalSteps μ r hr) r
        (swapDiagonalSteps_vertex μ r hr)).1 i = μ.1 i := by
      intro i; by_cases hi : i = r <;> simp +decide only [hi, ne_eq, not_false_eq_true,
          swapDiagonalSteps_apply_ne_r];
      let rm1 : Fin ((p) + (q)) := ⟨r.val - 1, by
        have := isDiagonalVertex_bounds hr
        omega⟩
      have h₁ := swapDiagonalSteps_val_r μ r hr rm1 rfl
      have h₂ := swapDiagonalSteps_val_r (swapDiagonalSteps μ r hr) r (swapDiagonalSteps_vertex μ r
          hr) rm1 rfl
      have htoggle : isLeftStep (swapDiagonalSteps μ r hr) rm1 ↔ ¬ isLeftStep μ rm1 := by
        simpa only [rm1] using swapDiagonalSteps_isLeftStep_toggle μ r hr
      by_cases hL : isLeftStep μ rm1
      · have hS : ¬ isLeftStep (swapDiagonalSteps μ r hr) rm1 := by
          exact fun hs => (htoggle.mp hs) hL
        rw [h₂]
        simp only [hS, ↓reduceDIte, h₁, hL, add_tsub_cancel_right, Fin.eta, rm1]
        exact Prod.ext (Fin.ext (Nat.sub_add_cancel
          (Nat.one_le_of_lt (diagonal_left_fst_pos hr hL)))) rfl
      · have hS : isLeftStep (swapDiagonalSteps μ r hr) rm1 := by
          exact htoggle.mpr hL
        rw [h₂]
        simp only [hS, ↓reduceDIte, h₁, hL, add_tsub_cancel_right, Fin.eta, rm1]
        exact Prod.ext rfl (Fin.ext (Nat.sub_add_cancel
          (Nat.one_le_of_lt (diagonal_right_snd_pos hr hL))))
    exact OrderHom.ext _ _ (funext h_swap)
  · rfl


/-- The sum `invCount(μ') + invCount(μ)` is odd, where `μ' = swapDiagonalSteps μ r hr`.

Proof sketch: rewrite both invCounts via `invCount_eq_sum_mul_diff` as sums over
`Fin ((p+1)+(q+1))`.  The swap only changes `μ.1` at position `r`, so the only
affected summands are at `s = ⟨r.val - 1, _⟩` (where `Fin.succ s = r`) and
`s = ⟨r.val, _⟩` (where `Fin.castSucc s = r`).  All other summands are equal
for `μ` and `μ'`, so they contribute an even amount to the combined sum.

For the two affected summands, set `y := (μ.1 ⟨r-1⟩).2.val`.  In the LR case
(step `r-1` is Left): the four terms are `y, 0, 0, y+1`, summing to `2y+1`.
In the RL case (step `r-1` is Right): the four terms are `0, y, y+1, 0`,
also summing to `2y+1`.  Hence the total is even + odd = odd. -/
private lemma swapDiagonalSteps_invCount_sum_odd {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) :
    Odd ((swapDiagonalSteps μ r hr).invCount + μ.invCount) := by
  rw [Shuffle.invCount_eq_sum_mul_diff, Shuffle.invCount_eq_sum_mul_diff,
    ← Finset.sum_add_distrib]
  let rm1 : Fin ((p) + (q)) := ⟨r.val - 1, by
    have := isDiagonalVertex_bounds hr; omega⟩
  let r' : Fin ((p) + (q)) := ⟨r.val, by
    have := isDiagonalVertex_bounds hr; omega⟩
  have hne : rm1 ≠ r' := by
    simp only [rm1, r', ne_eq, Fin.mk.injEq]
    have := isDiagonalVertex_bounds hr; omega
  rw [← Finset.sum_sdiff (s₁ := {rm1, r'}) (Finset.subset_univ _),
      Finset.sum_pair hne]
  have h_eq : ∀ x ∈ Finset.univ \ ({rm1, r'} : Finset _),
      ((μ.swapDiagonalSteps r hr).1 x.castSucc).2.val *
          (((μ.swapDiagonalSteps r hr).1 x.succ).1.val -
            ((μ.swapDiagonalSteps r hr).1 x.castSucc).1.val) +
        (μ.1 x.castSucc).2.val * ((μ.1 x.succ).1.val - (μ.1 x.castSucc).1.val) =
      2 * ((μ.1 x.castSucc).2.val * ((μ.1 x.succ).1.val - (μ.1 x.castSucc).1.val)) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_and, not_or] at hx
    rw [swapDiagonalSteps_apply_ne μ r hr x.castSucc (by
          intro h; exact absurd (Fin.ext (show x.val = r'.val by
            have := congr_arg Fin.val h
            simpa using this) : x = r') hx.2),
        swapDiagonalSteps_apply_ne μ r hr x.succ (by
          intro h; exact absurd (Fin.ext (show x.val = rm1.val by
            have := congr_arg Fin.val h
            simp only [Fin.val_succ] at this
            change x.val = r.val - 1; omega) : x = rm1) hx.1)]
    ring
  rw [Finset.sum_congr rfl h_eq, ← Finset.mul_sum]
  apply Even.add_odd (even_two_mul _)
  rw [swapDiagonalSteps_apply_ne μ r hr rm1.castSucc (by
        simp only [rm1, ne_eq, Fin.ext_iff, Fin.val_castSucc]
        have := isDiagonalVertex_bounds hr; omega),
      swapDiagonalSteps_apply_ne μ r hr r'.succ (by
        simp only [r', ne_eq, Fin.ext_iff, Fin.val_succ]
        omega)]
  by_cases hL : isLeftStep μ ⟨r.val - 1, by have := isDiagonalVertex_bounds hr; omega⟩
  · have hrm1_succ : rm1.succ = r := Fin.ext (by simp [rm1]; have := isDiagonalVertex_bounds hr;
                                                  omega)
    have hr'_castSucc : r'.castSucc = r := Fin.ext (by simp [r'])
    rw [hrm1_succ, hr'_castSucc, swapDiagonalSteps_apply_r_of_left μ r hr hL]
    have hstep_rm1 := shuffle_step μ ⟨r.val - 1, by
      have := isDiagonalVertex_bounds hr; omega⟩
    have hcs_rm1 : (⟨r.val - 1, by have := isDiagonalVertex_bounds hr; omega⟩ :
        Fin ((p) + (q))).castSucc = rm1.castSucc := by
      ext; simp [rm1]
    have hsucc_rm1 : (⟨r.val - 1, by have := isDiagonalVertex_bounds hr; omega⟩ :
        Fin ((p) + (q))).succ = r := by
      ext; simp; have := isDiagonalVertex_bounds hr; omega
    rw [hcs_rm1, hsucc_rm1] at hstep_rm1
    have hfst : (μ.1 rm1.castSucc).1.val + 1 = (μ.1 r).1.val := by
      rcases hstep_rm1 with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact h1
      · exfalso; unfold isLeftStep at hL; rw [hcs_rm1, hsucc_rm1] at hL; omega
    have hsnd : (μ.1 rm1.castSucc).2.val = (μ.1 r).2.val := by
      rcases hstep_rm1 with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · exfalso; unfold isLeftStep at hL; rw [hcs_rm1, hsucc_rm1] at hL; omega
    -- Step r is Right (diagonal: r-1 is Left, r is Right), so fst doesn't change
    have hstep_r := shuffle_step μ ⟨r.val, by
      have := isDiagonalVertex_bounds hr; omega⟩
    have hcs_r : (⟨r.val, by have := isDiagonalVertex_bounds hr; omega⟩ :
        Fin ((p) + (q))).castSucc = r := Fin.ext (by simp)
    have hsucc_r : (⟨r.val, by have := isDiagonalVertex_bounds hr; omega⟩ :
        Fin ((p) + (q))).succ = r'.succ := Fin.ext (by simp [r'])
    rw [hcs_r, hsucc_r] at hstep_r
    have hnotL_r : ¬isLeftStep μ ⟨r.val, (isDiagonalVertex_bounds hr).2⟩ := by
      unfold isDiagonalVertex at hr
      simp [(isDiagonalVertex_bounds hr).1, (isDiagonalVertex_bounds hr).2] at hr
      tauto
    have hfst_r : (μ.1 r'.succ).1.val = (μ.1 r).1.val := by
      rcases hstep_r with ⟨h1, _⟩ | ⟨h1, _⟩
      · exfalso; unfold isLeftStep at hnotL_r; rw [hcs_r, hsucc_r] at hnotL_r
        exact hnotL_r (by omega)
      · omega
    simp only at *
    -- Substitute: fst diff at rm1 is 0 and 1; fst diff at r' is 1 and 0
    have h1 : (μ.1 r).1.val - 1 - (μ.1 rm1.castSucc).1.val = 0 := by omega
    have h2 : (μ.1 r).1.val - (μ.1 rm1.castSucc).1.val = 1 := by omega
    have h3 : (μ.1 r'.succ).1.val - ((μ.1 r).1.val - 1) = 1 := by
      have := diagonal_left_fst_pos hr hL; omega
    have h4 : (μ.1 r'.succ).1.val - (μ.1 r).1.val = 0 := by omega
    rw [h1, h2, h3, h4]
    simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero]
    rw [← hsnd]
    exact ⟨(μ.1 rm1.castSucc).2.val, by omega⟩
  · have hrm1_succ : rm1.succ = r := Fin.ext (by
      simp [rm1]; have := isDiagonalVertex_bounds hr; omega)
    have hr'_castSucc : r'.castSucc = r := Fin.ext (by simp [r'])
    rw [hrm1_succ, hr'_castSucc, swapDiagonalSteps_apply_r_of_right μ r hr hL]
    have hstep_rm1 := shuffle_step μ ⟨r.val - 1, by
      have := isDiagonalVertex_bounds hr; omega⟩
    have hcs_rm1 : (⟨r.val - 1, by have := isDiagonalVertex_bounds hr; omega⟩ :
        Fin ((p) + (q))).castSucc = rm1.castSucc := by
      ext; simp [rm1]
    have hsucc_rm1 : (⟨r.val - 1, by have := isDiagonalVertex_bounds hr; omega⟩ :
        Fin ((p) + (q))).succ = r := by
      ext; simp; have := isDiagonalVertex_bounds hr; omega
    rw [hcs_rm1, hsucc_rm1] at hstep_rm1
    have hfst : (μ.1 rm1.castSucc).1.val = (μ.1 r).1.val := by
      rcases hstep_rm1 with ⟨h1, _⟩ | ⟨h1, _⟩
      · exfalso; unfold isLeftStep at hL; rw [hcs_rm1, hsucc_rm1] at hL
        exact hL (by omega)
      · exact h1
    have hsnd : (μ.1 rm1.castSucc).2.val + 1 = (μ.1 r).2.val := by
      rcases hstep_rm1 with ⟨h1, _⟩ | ⟨_, h2⟩
      · exfalso; unfold isLeftStep at hL; rw [hcs_rm1, hsucc_rm1] at hL
        exact hL (by omega)
      · exact h2
    have hstep_r := shuffle_step μ ⟨r.val, by
      have := isDiagonalVertex_bounds hr; omega⟩
    have hcs_r : (⟨r.val, by have := isDiagonalVertex_bounds hr; omega⟩ :
        Fin ((p) + (q))).castSucc = r := Fin.ext (by simp)
    have hsucc_r : (⟨r.val, by have := isDiagonalVertex_bounds hr; omega⟩ :
        Fin ((p) + (q))).succ = r'.succ := Fin.ext (by simp [r'])
    rw [hcs_r, hsucc_r] at hstep_r
    have hisL_r : isLeftStep μ ⟨r.val, (isDiagonalVertex_bounds hr).2⟩ := by
      unfold isDiagonalVertex at hr
      grind
    have hfst_r : (μ.1 r'.succ).1.val = (μ.1 r).1.val + 1 := by
      rcases hstep_r with ⟨h1, _⟩ | ⟨h1, _⟩
      · omega
      · unfold isLeftStep at hisL_r; rw [hcs_r, hsucc_r] at hisL_r; omega
    grind


/-- The swap negates the signed coefficient.

Derives from `swapDiagonalSteps_invCount_sum_odd`: since the invCount sum is
odd, `(-1)^invCount' * (-1)^invCount = -1`, and multiplying both sides by
`(-1)^invCount` (which squares to 1) gives `(-1)^invCount' = -(-1)^invCount`. -/
@[grind =]
lemma swapDiagonalSteps_neg_sign {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) :
    (swapDiagonalSteps μ r hr).sign  =
    -(μ.sign) := by
  unfold sign
  have key : (-1 : ℤ) ^ (swapDiagonalSteps μ r hr).invCount *
      (-1 : ℤ) ^ μ.invCount = -1 := by
    rw [← pow_add]; exact Odd.neg_one_pow (swapDiagonalSteps_invCount_sum_odd μ r hr)
  have sq : (-1 : ℤ) ^ μ.invCount * (-1 : ℤ) ^ μ.invCount = 1 := by
    rw [← mul_pow]; norm_num
  grind

/-- The swap involution is never the identity: swapping two steps of different
type always produces a distinct shuffle. -/
lemma swapDiagonalSteps_ne {p q : ℕ}
    (μ : Shuffle (p) (q)) (r : Index (p + (q)))
    (hr : isDiagonalVertex μ r) :
    swapDiagonalSteps μ r hr ≠ μ := by
  apply mt (congrArg Shuffle.sign)
  grind [Int.neg_one_pow_ne_zero, Shuffle.sign]



end Shuffle

end D5.S3.HomologicalAlgebra.EilenbergZilber
