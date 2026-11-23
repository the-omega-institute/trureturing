/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactHalfLogBounds
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Upper endpoints for the reflected half-log slope in the compact BMV chamber. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripMarginal
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MixedNormalization
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactRegularizedRadical
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapJ
import Batteries.Tactic.OpenPrivate

namespace RefinedBMV.PositiveCenter

open private negativeMarginal_logDeriv_of_exponent_bound tilted_gap_slope_le from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripMarginal

open private M M_zero M_mass_zero M_pos M_logConvex hasDerivAt_M
  variance_eq gapCount gapCount_pos varianceHalf from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapJ

open private compactKappa_eq_varianceHalf from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactRegularizedRadical

private theorem integralSlope_monotone {p : ℕ} (hp : 0 < p) :
    Monotone (fun x ↦ M p 1 x / M p 0 x) := by
  have hd (x : ℝ) : HasDerivAt (fun y ↦ M p 1 y / M p 0 y)
      ((M p 2 x * M p 0 x - M p 1 x ^ 2) / M p 0 x ^ 2) x := by
    convert (hasDerivAt_M p 1 x).div (hasDerivAt_M p 0 x) (M_pos hp x).ne' using 1
    ring
  refine monotone_of_deriv_nonneg (fun x ↦ (hd x).differentiableAt) fun x ↦ ?_
  rw [(hd x).deriv]
  exact div_nonneg (sub_nonneg.mpr (by simpa only [mul_comm] using M_logConvex hp x))
    (sq_nonneg _)

private theorem compactZSlope_eq_integralSlope {p : ℕ} (hp : 0 < p) (t : ℝ) :
    compactZSlope p t = M p 1 t / M p 0 t := by
  rw [compactZSlope_eq hp, compactZ, compactKappa_eq_varianceHalf hp]

private theorem compactZSlope_nonpos_argument_le_zero_slope {p : ℕ} (hp : 0 < p) {t : ℝ}
    (ht : 0 ≤ t) : compactZSlope p (-t) ≤ (2 + 3 / (p : ℝ)) / 15 := by
  have hMoment : M p 1 0 = (2 + 3 / (p : ℝ)) / 15 := by
    rw [M_zero, show (1 : ℕ) + 2 = 3 by decide, centered_marginal_cubic_sum hp]
    simp only [gapCount, varianceHalf, Nat.cast_one]
    rw [variance_eq hp]
    have hP : (0 : ℝ) < p := by exact_mod_cast hp
    have hN : (0 : ℝ) < (DimThree.gaps p).length := gapCount_pos p
    field_simp [hP.ne', hN.ne']
    <;> ring
  rw [compactZSlope_eq_integralSlope hp, ← hMoment]
  have h := integralSlope_monotone hp (neg_nonpos.mpr ht)
  change M p 1 (-t) / M p 0 (-t) ≤ M p 1 0 / M p 0 0 at h
  rwa [M_mass_zero, div_one] at h

/-- Log-convexity of the regularized marginal bounds the reflected slope from below. -/
theorem reflectedHalfLogSlope_ge_inv_sub_five_sixty_sixths {p : ℕ} (hp : 11 ≤ p) {t : ℝ}
    (ht : 0 < t) : 1 / t - 5 / 66 ≤ reflectedHalfLogSlope (compositionMoment p 0) t := by
  have hp₀ : 0 < p := by omega
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hSpacing : 3 / (p : ℝ) ≤ 3 / 11 := by
    rw [div_le_iff₀ (show (0 : ℝ) < p by linarith)]
    linarith only [hpR]
  rw [reflectedHalfLogSlope_eq_compactZSlope hp₀ ht.ne']
  linarith only [compactZSlope_nonpos_argument_le_zero_slope hp₀ ht.le, hSpacing]

/-- The lower bound through coordinate two. -/
theorem reflectedHalfLogSlope_ge_five_twelfths_of_le_two {p : ℕ} (hp : 11 ≤ p) {t : ℝ}
    (ht : 0 < t) (htMax : t ≤ 2) :
    5 / 12 ≤ reflectedHalfLogSlope (compositionMoment p 0) t := by
  have hInv : (1 : ℝ) / 2 ≤ 1 / t := one_div_le_one_div_of_le ht htMax
  linarith only [reflectedHalfLogSlope_ge_inv_sub_five_sixty_sixths hp ht, hInv]

private theorem advance_reflectedHalfLogSlope {p : ℕ} (hp : 0 < p) {a t : ℝ}
    (ha : 0 < a) (hat : a ≤ t) :
    reflectedHalfLogSlope (compositionMoment p 0) a + 1 / t - 1 / a ≤
      reflectedHalfLogSlope (compositionMoment p 0) t := by
  rw [reflectedHalfLogSlope_eq_compactZSlope hp ha.ne',
    reflectedHalfLogSlope_eq_compactZSlope hp (ha.trans_le hat).ne',
    compactZSlope_eq_integralSlope hp, compactZSlope_eq_integralSlope hp]
  have h := integralSlope_monotone hp (neg_le_neg hat)
  change M p 1 (-t) / M p 0 (-t) ≤ M p 1 (-a) / M p 0 (-a) at h
  linarith only [h]

/-- The two fixed-coordinate estimates suffice for the remaining lower slope bound. -/
theorem reflectedHalfLogSlope_ge_five_twelfths_of_checkpoints {p : ℕ} (hp : 11 ≤ p)
    (hTwo : 23 / 40 ≤ reflectedHalfLogSlope (compositionMoment p 0) 2)
    (hLater : 1159 / 2436 ≤ reflectedHalfLogSlope (compositionMoment p 0) (29 / 10))
    {t : ℝ} (ht : 0 < t) : 5 / 12 ≤ reflectedHalfLogSlope (compositionMoment p 0) t := by
  have hp₀ : 0 < p := by omega
  by_cases h₂ : t ≤ 2
  · exact reflectedHalfLogSlope_ge_five_twelfths_of_le_two hp ht h₂
  by_cases h₃ : t ≤ 29 / 10
  · have hs := advance_reflectedHalfLogSlope hp₀ (a := 2) (by norm_num) (le_of_not_ge h₂)
    have hi := one_div_le_one_div_of_le ht h₃
    linarith only [hs, hi, hTwo]
  by_cases hLast : t ≤ 7 / 2
  · have hs := advance_reflectedHalfLogSlope hp₀ (a := 29 / 10) (by norm_num) (le_of_not_ge h₃)
    have hi := one_div_le_one_div_of_le ht hLast
    linarith only [hs, hi, hLater]
  · have hs := negativeMarginal_logDeriv_ge_seven_halves hp₀ (le_of_not_ge hLast)
    unfold reflectedHalfLogSlope
    linarith only [hs]

private theorem reflectedSlope_le_exp_quotient {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    reflectedHalfLogSlope (compositionMoment p 0) t ≤
      (Real.exp t - 1) / (Real.exp t - 1 - t) / 2 := by
  let K := (Real.exp t - 1) / (Real.exp t - 1 - t)
  unfold reflectedHalfLogSlope
  apply div_le_div_of_nonneg_right _ (by norm_num)
  refine negativeMarginal_logDeriv_of_exponent_bound hp ht (m := 1 - K * t) ?_
  intro x hx
  have h := tilted_gap_slope_le ht hx
  change x * (Real.exp (x * t) - 1) ≤ K * (Real.exp (x * t) - 1 - x * t) at h
  nlinarith only [h]

/-- A polynomial upper bound on the exponential quotient for any positive coordinate. -/
theorem reflectedHalfLogSlope_le_inv_add_linear {p : ℕ} (hp : 0 < p) {t : ℝ}
    (ht : 0 < t) :
    reflectedHalfLogSlope (compositionMoment p 0) t ≤ 1 / t + 1 / 6 + t / 30 := by
  have hE : 0 < Real.exp t - 1 - t := by linarith [Real.add_one_lt_exp ht.ne']
  have hTaylor := Real.sum_le_exp_of_nonneg ht.le 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at hTaylor
  have hcoef : 0 ≤ t ^ 2 - 10 * t + 30 := by nlinarith only [sq_nonneg (t - 5)]
  have hpoly : 0 ≤ t ^ 4 / 12 + t ^ 7 / 2520 + t ^ 8 * ((t - 1) ^ 2 + 5) / 40320 := by
    positivity
  have hpos : t * (30 + 5 * t + t ^ 2) ≤ (t ^ 2 - 10 * t + 30) * (Real.exp t - 1) := by
    have h := mul_le_mul_of_nonneg_left hTaylor hcoef
    nlinarith only [h, hpoly]
  refine (reflectedSlope_le_exp_quotient hp ht).trans ?_
  apply (mul_le_mul_iff_left₀ (mul_pos ht hE)).mp
  field_simp [ht.ne', hE.ne']
  nlinarith only [hpos]

/-- The slope for the lower coordinate on the middle strip. -/
theorem reflectedHalfLogSlope_le_inv_add_three_tenths {p : ℕ} (hp : 0 < p) {t : ℝ}
    (ht : 0 < t) (htmax : t ≤ 4) :
    reflectedHalfLogSlope (compositionMoment p 0) t ≤ 1 / t + 3 / 10 := by
  linarith only [reflectedHalfLogSlope_le_inv_add_linear hp ht, htmax]

/-- The upper-coordinate slope from the start of the second gap band. -/
theorem reflectedHalfLogSlope_le_thirteen_twentieths_of_five_halves_le
    {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 5 / 2 ≤ t) :
    reflectedHalfLogSlope (compositionMoment p 0) t ≤ 13 / 20 := by
  have ht₀ : 0 < t := by linarith
  have hTaylor := Real.sum_le_exp_of_nonneg ht₀.le 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at hTaylor
  have hpoly : 13 / 3 ≤ 1 + t / 2 + t ^ 2 / 6 + t ^ 3 / 24 + t ^ 4 / 120 + t ^ 5 / 720 := by
    have hpow (n : ℕ) : (5 / 2 : ℝ) ^ n ≤ t ^ n := by gcongr
    norm_num at *
    linarith only [ht, hpow 2, hpow 3, hpow 4, hpow 5]
  have hBound : 13 * t / 3 ≤ Real.exp t - 1 := by
    nlinarith only [hTaylor, mul_le_mul_of_nonneg_right hpoly ht₀.le]
  have hDen : 0 < Real.exp t - 1 - t := by linarith
  refine (reflectedSlope_le_exp_quotient hp ht₀).trans ?_
  rw [div_div, div_le_iff₀ (mul_pos hDen (by norm_num))]
  linarith only [hBound]

/-- The slope for the upper coordinate when the separation is at least one. -/
theorem reflectedHalfLogSlope_le_one_of_three_halves_le {p : ℕ} (hp : 0 < p) {t : ℝ}
    (ht : 3 / 2 ≤ t) : reflectedHalfLogSlope (compositionMoment p 0) t ≤ 1 := by
  have ht₀ : 0 < t := by linarith
  have hTaylor := Real.sum_le_exp_of_nonneg ht₀.le 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at hTaylor
  have hsq : (9 / 4 : ℝ) ≤ t ^ 2 := by nlinarith
  have hpos : 0 ≤ t / 2 + t ^ 2 / 6 - 1 := by linarith
  have hE : 2 * t ≤ Real.exp t - 1 := by nlinarith only [hTaylor, mul_nonneg ht₀.le hpos]
  have hden : 0 < Real.exp t - 1 - t := by linarith
  refine (reflectedSlope_le_exp_quotient hp ht₀).trans ?_
  rw [div_div, div_le_iff₀ (mul_pos hden (by norm_num))]
  linarith

end RefinedBMV.PositiveCenter
