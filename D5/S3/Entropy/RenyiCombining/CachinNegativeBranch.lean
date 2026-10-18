/- GID: D5/S3/Entropy/RenyiCombining/CachinNegativeBranch
   generality: G
   mirror-B: D5/B/S3/Entropy/RenyiCombining/CachinNegativeBranch
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Negative-order real-power elasticity certificate for Renyi information combining. -/

import D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone

open Set
open D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone

namespace D5.S3.Entropy.RenyiCombining.CachinNegativeBranch

private theorem power_gt_one (n r : ℝ) (hn : n < 0) (hr : r ∈ Ioo 0 1) :
    1 < r ^ n := by
  have h := Real.rpow_lt_rpow_of_exponent_gt hr.1 hr.2 hn
  simpa using h

private theorem T_neg (n r : ℝ) (hn : n < 0) (hr : r ∈ Ioo 0 1) :
    T n r < 0 := by
  have hp := power_gt_one n r hn hr
  exact div_neg_of_neg_of_pos (by linarith) (by linarith)

private theorem A_pos (n r : ℝ) (hn : n < 0) (hr : r ∈ Ioo 0 1) :
    0 < A n r := by
  rw [A_eq n r hr.1]
  have hp := power_gt_one n r hn hr
  exact div_pos_of_neg_of_neg
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hn (Real.rpow_pos_of_pos hr.1 _))
      (by nlinarith [hr.1, hr.2]))
    (mul_neg_of_neg_of_pos (by linarith) (by linarith))

private theorem B_bounds (n r : ℝ) (hn : n < 0) (hr : r ∈ Ioo 0 1) :
    -1 < B n r ∧ B n r < 0 := by
  have hp := Real.rpow_pos_of_pos hr.1 n
  have ht := T_neg n r hn hr
  have ht₀ : -1 < T n r := by
    dsimp [T]
    apply (lt_div_iff₀ (by linarith : 0 < 1 + r ^ n)).mpr
    linarith
  have hτ₀ : 0 < (1 - r) / (1 + r) := div_pos (by linarith [hr.2]) (by linarith [hr.1])
  have hτ₁ : (1 - r) / (1 + r) < 1 := by
    apply (div_lt_one (by linarith [hr.1] : 0 < 1 + r)).mpr
    linarith [hr.1]
  have hprod : T n r < ((1 - r) / (1 + r)) * T n r := by nlinarith
  exact ⟨ht₀.trans hprod, mul_neg_of_pos_of_neg hτ₀ ht⟩

private theorem B₁_pos (n r : ℝ) (hn : n < 0) (hr : r ∈ Ioo 0 1) :
    0 < B₁ n r := by
  have ht := T_neg n r hn hr
  have hp := Real.rpow_pos_of_pos hr.1 n
  have hτ : 0 < (1 - r) / (1 + r) := div_pos (by linarith [hr.2]) (by linarith [hr.1])
  have hfirst : 0 < -2 * T n r / (1 + r) ^ (2 : ℕ) :=
    div_pos (mul_pos_of_neg_of_neg (by norm_num) ht) (sq_pos_of_pos (by linarith [hr.1]))
  have hsecond : 2 * n * ((1 - r) / (1 + r)) * r ^ (n - 1) /
      (1 + r ^ n) ^ (2 : ℕ) < 0 :=
    div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hτ)
        (Real.rpow_pos_of_pos hr.1 _)) (sq_pos_of_pos (by linarith))
  dsimp [B₁]
  linarith

private theorem A₁_nonpos (n r : ℝ) (hn₀ : -1 < n) (hn₁ : n < 0)
    (hr : r ∈ Ioo 0 1) : A₁ n r ≤ 0 := by
  have hr₂ : r ^ (2 : ℕ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨sq_pos_of_pos hr.1, by nlinarith [hr.1, hr.2]⟩
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hn₁.le (Real.rpow_nonneg hr.1.le _))
      (J_nonneg n _ (mul_nonneg_of_nonpos_of_nonpos hn₁.le (by nlinarith)) hr₂)) (sq_nonneg _)

private theorem F₁_neg (n r : ℝ) (hn₀ : -1 < n) (hn₁ : n < 0)
    (hr : r ∈ Ioo 0 1) : F₁ n r < 0 := by
  have hA := A_pos n r hn₁ hr
  have hB := (B_bounds n r hn₁ hr).1
  have hA₁ := A₁_nonpos n r hn₀ hn₁ hr
  have hB₁ := B₁_pos n r hn₁ hr
  have hfirst : A₁ n r / (1 + B n r) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hA₁ (by linarith)
  have hsecond : 0 < (1 + A n r) * B₁ n r / (1 + B n r) ^ (2 : ℕ) :=
    div_pos (mul_pos (by linarith) hB₁) (sq_pos_of_pos (by linarith))
  dsimp [F₁]
  linarith

theorem antitoneOn_F_neg (n : ℝ) (hn₀ : -1 < n) (hn₁ : n < 0) :
    AntitoneOn (F n) (Ioo 0 1) := by
  apply (strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    (fun r hr => (F_hasDerivAt n r hn₁.ne hr
      (by have h := (B_bounds n r hn₁ hr).1; linarith)).continuousAt.continuousWithinAt) _).antitoneOn
  intro r hr
  have hr' : r ∈ Ioo (0 : ℝ) 1 := interior_subset hr
  rw [(F_hasDerivAt n r hn₁.ne hr'
    (by have h := (B_bounds n r hn₁ hr').1; linarith)).deriv]
  exact F₁_neg n r hn₀ hn₁ hr'

end D5.S3.Entropy.RenyiCombining.CachinNegativeBranch
