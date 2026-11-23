/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ShortGapTenThirdsAbsorption
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The four scalar bounds that absorb the positive radical derivative. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapSign

namespace RefinedBMV.PositiveCenter

private theorem exp_neg_ten_thirds_lt : Real.exp (-(10 / 3 : ℝ)) < 1 / 28 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 10 / 3) 11
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg, one_div, inv_lt_inv₀ (Real.exp_pos _) (by norm_num)]
  linarith only [h]

private theorem exp_neg_four_lt : Real.exp (-4 : ℝ) < 1 / 52 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg, one_div, inv_lt_inv₀ (Real.exp_pos _) (by norm_num)]
  linarith only [h]

private theorem exp_neg_five_lt : Real.exp (-5 : ℝ) < 1 / 148 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5) 13
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg, one_div, inv_lt_inv₀ (Real.exp_pos _) (by norm_num)]
  linarith only [h]

private theorem linear_mul_exp_neg_le {u a : ℝ} (hu : 10 / 3 ≤ u) (ha : 0 ≤ a) :
    (u + a) * Real.exp (-u) ≤ (10 / 3 + a) / 28 := by
  have h₀ : 0 ≤ u - 10 / 3 := by linarith
  have h₁ : 0 ≤ (10 / 3 + a) - 1 := by linarith
  have h₂ : u + a ≤ (10 / 3 + a) * Real.exp (u - 10 / 3) := calc
    _ ≤ (10 / 3 + a) * (1 + (u - 10 / 3)) := by
      nlinarith only [mul_nonneg h₁ h₀]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [Real.add_one_le_exp (u - 10 / 3)])
      (by linarith only [ha])
  calc
    _ ≤ ((10 / 3 + a) * Real.exp (u - 10 / 3)) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right h₂ (Real.exp_pos _).le
    _ = (10 / 3 + a) * Real.exp (-(10 / 3)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left exp_neg_ten_thirds_lt.le (by linarith only [ha])

/-- The normalization margin dominates the combined derivative bound on the enlarged strip. -/
theorem shortGapTenThirds_absorption_scalar {u v μG z : ℝ}
    (hu : 10 / 3 ≤ u) (huv : u < v) (hd : v - u ≤ 2)
    (hG₀ : 0 ≤ μG) (hGsmall : v ≤ 4 → μG ≤ (120 / 113) * (157 / 52))
    (hGlarge : 4 ≤ v → μG ≤ (120 / 113) * (v - 1 + Real.exp (-v)))
    (hz₀ : 24 / 25 ≤ z) (hz₄ : 4 ≤ v → 50 / 51 ≤ z)
    (hz₅ : 5 ≤ v → 997 / 1000 ≤ z) :
    (if v - u ≤ 1 then 1 else (43 / 50 : ℝ)) * μG * Real.exp (-u) <
      z * ((1 - 1 / u) * (1 - 1 / v) / 4) := by
  let ρ : ℝ := if v - u ≤ 1 then 1 else 43 / 50
  have hu₀ : 0 < u := by linarith
  have hv₀ : 0 < v := hu₀.trans huv
  have hb : 0 < u - 1 := by linarith
  have hc : 0 < v - 1 := by linarith
  have hz : 0 < z := by linarith only [hz₀]
  have hρ : 0 ≤ ρ := by unfold ρ; split <;> norm_num
  have hρ₁ : ρ ≤ 1 := by unfold ρ; split <;> norm_num
  have hU := Real.exp_le_exp.mpr (neg_le_neg hu)
  have heu : Real.exp (-u) ≤ 1 / 28 := hU.trans exp_neg_ten_thirds_lt.le
  change ρ * μG * Real.exp (-u) < _
  by_cases hv₄ : v ≤ 4
  · have hGu := hGsmall hv₄
    have htop : ρ * μG * Real.exp (-u) ≤ (1 : ℝ) * ((120 / 113) * (157 / 52)) * (1 / 28) :=
      mul_le_mul (mul_le_mul hρ₁ hGu hG₀ (by norm_num)) heu (Real.exp_pos _).le (by norm_num)
    have hiu : 1 / u ≤ (3 / 10 : ℝ) := by
      norm_num at hu ⊢
      exact (div_le_iff₀ hu₀).mpr (by linarith)
    have hiv : 1 / v ≤ (3 / 10 : ℝ) :=
      (one_div_le_one_div_of_le hu₀ huv.le).trans hiu
    have hbottom : ((24 / 25 : ℝ) * ((7 / 10) * (7 / 10) / 4)) ≤
        z * ((1 - 1 / u) * (1 - 1 / v) / 4) := by
      apply mul_le_mul hz₀ _ (by norm_num) hz.le
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul (by linarith only [hiu]) (by linarith only [hiv])
        (by norm_num) (by linarith only [hiu])
    exact htop.trans_lt ((by norm_num : (1 : ℝ) * ((120 / 113) * (157 / 52)) *
      (1 / 28) < (24 / 25) * ((7 / 10) * (7 / 10) / 4)).trans_le hbottom)
  have hv₄' : 4 ≤ v := le_of_lt (lt_of_not_ge hv₄)
  have hbnd : u / (u - 1) ≤ (10 / 7 : ℝ) :=
    (div_le_iff₀ hb).mpr (by linarith only [hu])
  have hr : 0 < (u / (u - 1)) * v := mul_pos (div_pos hu₀ hb) hv₀
  let M := (u / (u - 1)) * v * Real.exp (-u)
  let E := 1 + Real.exp (-v) / (v - 1)
  have hM₀ : 0 ≤ M := (mul_pos hr (Real.exp_pos _)).le
  have hE₀ : 0 ≤ E := by dsimp only [E]; positivity
  have hE₄ : E ≤ (157 / 156 : ℝ) := by
    have h := (Real.exp_le_exp.mpr (neg_le_neg hv₄')).trans exp_neg_four_lt.le
    have hx : Real.exp (-v) / (v - 1) ≤ (1 / 52 : ℝ) / 3 :=
      (div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num)
        (by linarith only [hv₄'])).trans (div_le_div_of_nonneg_right h (by norm_num))
    dsimp only [E]
    linarith only [hx]
  have hless : ρ * (480 / 113) * M * E < z := by
    by_cases hd₁ : v - u ≤ 1
    · have hM : M ≤ (65 / 294 : ℝ) := by
        have hv' : v * Real.exp (-u) ≤ (u + 1) * Real.exp (-u) :=
          mul_le_mul_of_nonneg_right (by linarith only [hd₁]) (Real.exp_pos _).le
        have hmax := hv'.trans (linear_mul_exp_neg_le hu (by norm_num : (0 : ℝ) ≤ 1))
        dsimp only [M]
        rw [mul_assoc]
        calc
          _ ≤ (10 / 7 : ℝ) * ((10 / 3 + 1) / 28) :=
            mul_le_mul hbnd hmax (mul_nonneg hv₀.le (Real.exp_pos _).le) (by norm_num)
          _ = _ := by norm_num
      rw [show ρ = 1 by simp [ρ, hd₁]]
      refine (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hM (by norm_num : 0 ≤ (1 : ℝ) * (480 / 113))) hE₀).trans_lt ?_
      exact (mul_le_mul_of_nonneg_left hE₄ (by norm_num)).trans_lt
        ((by norm_num : (1 : ℝ) * (480 / 113) * (65 / 294) * (157 / 156) < 50 / 51).trans_le
          (hz₄ hv₄'))
    have hρ' : ρ = 43 / 50 := by simp [ρ, hd₁]
    rw [hρ']
    by_cases hv₅ : v ≤ 5
    · have hve : v * Real.exp (-u) ≤ (5 / 28 : ℝ) := by
        calc
          _ ≤ (5 : ℝ) * (1 / 28) := mul_le_mul hv₅ heu (Real.exp_pos _).le (by norm_num)
          _ = _ := by norm_num
      have hM : M ≤ (25 / 98 : ℝ) := by
        dsimp only [M]
        rw [mul_assoc]
        exact (mul_le_mul hbnd hve (by positivity) (by norm_num)).trans_eq (by norm_num)
      calc
        _ ≤ (43 / 50 : ℝ) * (480 / 113) * (25 / 98) * (157 / 156) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hM (by norm_num)) hE₄ hE₀ (by norm_num)
        _ < (50 / 51 : ℝ) := by norm_num
        _ ≤ _ := hz₄ hv₄'
    have hv₅' : 5 ≤ v := le_of_lt (lt_of_not_ge hv₅)
    have hE₅ : E ≤ (593 / 592 : ℝ) := by
      have hvexp := (Real.exp_le_exp.mpr (neg_le_neg hv₅')).trans exp_neg_five_lt.le
      have he : Real.exp (-v) / (v - 1) ≤ (1 / 148 : ℝ) / 4 :=
        (div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num)
          (by linarith only [hv₅'])).trans (div_le_div_of_nonneg_right hvexp (by norm_num))
      dsimp only [E]
      linarith only [he]
    have hM : M ≤ (40 / 147 : ℝ) := by
      have hve : v * Real.exp (-u) ≤ (u + 2) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right (by linarith only [hd]) (Real.exp_pos _).le
      have hmax := hve.trans (linear_mul_exp_neg_le hu (by norm_num : (0 : ℝ) ≤ 2))
      dsimp only [M]
      rw [mul_assoc]
      exact (mul_le_mul hbnd hmax (by positivity) (by norm_num)).trans_eq (by norm_num)
    calc
      _ ≤ (43 / 50 : ℝ) * (480 / 113) * (40 / 147) * (593 / 592) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hM (by norm_num)) hE₅ hE₀ (by norm_num)
      _ < (997 / 1000 : ℝ) := by norm_num
      _ ≤ _ := hz₅ hv₅'
  have htop : ρ * μG * Real.exp (-u) ≤
      ρ * ((120 / 113 : ℝ) * (v - 1 + Real.exp (-v))) * Real.exp (-u) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hGlarge hv₄') hρ) (Real.exp_pos _).le
  have hfac : 0 < (u - 1) * (v - 1) / (4 * u * v) := by positivity
  have hscaled := mul_lt_mul_of_pos_right hless hfac
  have hleft : ρ * (480 / 113) * M * E * ((u - 1) * (v - 1) / (4 * u * v)) =
      ρ * ((120 / 113 : ℝ) * (v - 1 + Real.exp (-v))) * Real.exp (-u) := by
    dsimp only [M, E]
    field_simp [hu₀.ne', hv₀.ne', hb.ne', hc.ne'] <;> ring
  have hright : z * ((u - 1) * (v - 1) / (4 * u * v)) =
      z * ((1 - 1 / u) * (1 - 1 / v) / 4) := by
    field_simp [hu₀.ne', hv₀.ne'] <;> ring
  rw [hleft, hright] at hscaled
  exact htop.trans_lt hscaled

end RefinedBMV.PositiveCenter
