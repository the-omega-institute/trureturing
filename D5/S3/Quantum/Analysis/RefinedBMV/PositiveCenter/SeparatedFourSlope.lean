/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/SeparatedFourSlope
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharper upper-tail slope and ratio estimates for the central strip at gap four. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.UpperTail
import D5.S3.Observer.Fluctuation.ThermalCoefficientFloor
import Mathlib.Tactic.LinearCombination

/-! # Upper-tail slope estimates for the central strip at gap four -/

open Filter Set
open scoped Topology

namespace RefinedBMV.PositiveCenter

open private deriv_deriv_upperTailSlope from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.UpperTail

private theorem sinh_cosh_comparison {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x * (3 + 2 * Real.sinh x ^ 2) - 3 * Real.sinh x * Real.cosh x := by
  let F (y : ℝ) := y * (3 + 2 * Real.sinh y ^ 2) - 3 * Real.sinh y * Real.cosh y
  have hF (y : ℝ) :
      HasDerivAt F (4 * Real.sinh y * (y * Real.cosh y - Real.sinh y)) y := by
    have hs := Real.hasDerivAt_sinh y
    have hc := Real.hasDerivAt_cosh y
    have hd := ((hasDerivAt_id y).mul (((hs.pow 2).const_mul 2).const_add 3)).sub
      ((hs.const_mul 3).mul hc)
    change HasDerivAt F _ y at hd
    convert hd using 1
    simp only [id_eq, Pi.pow_apply, Nat.reduceSub, Nat.cast_ofNat]
    linear_combination
      (3 : ℝ) * Real.cosh_sq_sub_sinh_sq y
  have hmono : MonotoneOn F (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ ↦ (hF y).continuousAt.continuousWithinAt)
      (fun y _ ↦ (hF y).differentiableAt.differentiableWithinAt)
    intro y hy
    have hy₀ : 0 ≤ y := interior_subset hy
    rw [(hF y).deriv]
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.sinh_nonneg_iff.mpr hy₀))
      (sub_nonneg.mpr
        (D5.S3.Observer.Fluctuation.ThermalCoefficientFloor.sinh_le_self_mul_cosh_of_nonneg hy₀))
  simpa [F] using hmono (mem_Ici.mpr (le_refl (0 : ℝ))) hx hx

private theorem mul_cosh_le_sinh_cube {x : ℝ} (hx : 0 < x) :
    x ^ 3 * Real.cosh x ≤ Real.sinh x ^ 3 := by
  let R (y : ℝ) := Real.sinh y ^ 3 / (y ^ 3 * Real.cosh y)
  have hden {y : ℝ} (hy : 0 < y) : 0 < y ^ 3 * Real.cosh y :=
    mul_pos (pow_pos hy _) (Real.cosh_pos y)
  have hR {y : ℝ} (hy : 0 < y) :
      HasDerivAt R
        (y ^ 2 * Real.sinh y ^ 2 *
          (y * (3 + 2 * Real.sinh y ^ 2) - 3 * Real.sinh y * Real.cosh y) /
            (y ^ 3 * Real.cosh y) ^ 2) y := by
    have hd := ((Real.hasDerivAt_sinh y).pow 3).div
      (((hasDerivAt_id y).pow 3).mul (Real.hasDerivAt_cosh y)) (hden hy).ne'
    change HasDerivAt R _ y at hd
    convert hd using 1
    simp only [id_eq, Pi.mul_apply, Pi.pow_apply, Nat.reduceSub, Nat.cast_ofNat]
    congr 1
    linear_combination
      -(3 * y ^ 3 * Real.sinh y ^ 2) * Real.cosh_sq_sub_sinh_sq y
  have hmono : MonotoneOn R (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun y hy ↦ (hR hy).continuousAt.continuousWithinAt)
      (fun y hy ↦ (hR (interior_subset hy)).differentiableAt.differentiableWithinAt)
    intro y hy
    have hy₀ : 0 < y := interior_subset hy
    rw [(hR hy₀).deriv]
    exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (sinh_cosh_comparison hy₀.le)) (sq_nonneg _)
  have hs : Tendsto (fun y : ℝ ↦ Real.sinh y / y) (𝓝[>] 0) (𝓝 1) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_sinh 0).tendsto_slope_zero_right
  have hc : Tendsto Real.cosh (𝓝[>] 0) (𝓝 1) := by
    have h : Tendsto Real.cosh (𝓝[>] 0) (𝓝 (Real.cosh 0)) :=
      Real.continuous_cosh.continuousAt.continuousWithinAt
    simpa only [Real.cosh_zero] using h
  have hlim : Tendsto R (𝓝[>] 0) (𝓝 1) := by
    have hlim := (hs.pow 3).div hc one_ne_zero
    change Tendsto (fun y : ℝ ↦ (Real.sinh y / y) ^ 3 / Real.cosh y)
      (𝓝[>] 0) (𝓝 (1 ^ 3 / 1)) at hlim
    simpa only [one_pow, div_pow, div_div, div_one, R] using hlim
  have hbound : 1 ≤ R x := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0),
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hx)] with y hy hyx
    exact hmono hy hx hyx.le
  simpa only [one_mul] using (le_div_iff₀ (hden hx)).mp hbound

/-- The second derivative of the upper-tail slope is bounded by the second
derivative of the reciprocal gap. -/
theorem upperTailSlope_second_deriv_le {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    deriv (deriv (upperTailSlope h)) t ≤ 2 / t ^ 3 := by
  let x := h * t / 2
  have hx : 0 < x := by dsimp [x]; positivity
  have hs := Real.sinh_pos_iff.mpr hx
  have he := Real.exp_pos x
  have hexp : Real.exp (h * t) = Real.exp x ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    dsimp [x]
    ring
  have hminus : Real.exp (h * t) - 1 = 2 * Real.exp x * Real.sinh x := by
    rw [hexp, Real.sinh_eq, Real.exp_neg]
    field_simp [he.ne']
  have hplus : Real.exp (h * t) + 1 = 2 * Real.exp x * Real.cosh x := by
    rw [hexp, Real.cosh_eq, Real.exp_neg]
    field_simp [he.ne']
  have hgap : 0 < Real.exp (h * t) - 1 := by rw [hminus]; positivity
  calc
    deriv (deriv (upperTailSlope h)) t =
        h ^ 3 * Real.exp (h * t) * (Real.exp (h * t) + 1) /
          (Real.exp (h * t) - 1) ^ 3 := by
      rw [deriv_deriv_upperTailSlope hh ht]
      unfold upperTailSlope
      field_simp [hgap.ne']
      ring
    _ = h ^ 3 * Real.cosh x / (4 * Real.sinh x ^ 3) := by
      rw [hplus, hminus, hexp]
      field_simp [he.ne', hs.ne']
      ring
    _ ≤ 2 / t ^ 3 := by
      apply (div_le_div_iff₀ (by positivity) (pow_pos ht _)).2
      have hc := mul_cosh_le_sinh_cube hx
      dsimp [x] at hc
      linear_combination 8 * hc

private theorem reciprocal_sub_upperTailSlope_antitone {h : ℝ} (hh : 0 < h) :
    AntitoneOn (fun t : ℝ ↦ 1 / t - upperTailSlope h t) (Ioi 0) := by
  have hD {t : ℝ} (ht : 0 < t) :
      HasDerivAt (fun z : ℝ ↦ 1 / z - upperTailSlope h z)
        (-(1 / t ^ 2) + -deriv (upperTailSlope h) t) t := by
    have h := (hasDerivAt_inv ht.ne').sub (hasDerivAt_upperTailSlope hh ht)
    change HasDerivAt (fun z : ℝ ↦ z⁻¹ - upperTailSlope _ z) _ t at h
    simpa only [one_div, sub_eq_add_neg, neg_neg,
      (hasDerivAt_upperTailSlope hh ht).deriv] using h
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (fun t ht ↦ (hD ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hD (interior_subset ht)).differentiableAt.differentiableWithinAt)
  intro t ht
  have ht₀ : 0 < t := interior_subset ht
  rw [(hD ht₀).deriv]
  linarith only [(upperTailSlope_bounds hh ht₀).2.2.2.1]

private theorem exp_half_lt_127_div_77 : Real.exp (1 / 2) < 127 / 77 := by
  have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  by_contra! h
  have hle := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 127 / 77) h 2
  rw [hsq] at hle
  exact (not_lt_of_ge hle) (Real.exp_one_lt_d9.trans (by norm_num))

/-- The actual derivative of the leading-square ratio decays at a uniform
relative rate for lower coordinate at least one half. -/
theorem upperTailRatio_deriv_le_neg_mul {h u : ℝ} (hh : 0 < h) (hu : 1 / 2 ≤ u) :
    deriv (upperTailRatio h) u ≤ -(27 / 50) * upperTailRatio h u := by
  have hu₀ : 0 < u := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hu
  have hden : 0 < Real.exp u - 1 := sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr hu₀)
  have hhalf : 0 < Real.exp (1 / 2) - 1 := by
    apply sub_pos.mpr
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  have hhalfBound : 27 / 50 + 1 ≤ 1 / (Real.exp (1 / 2) - 1) := by
    apply (le_div_iff₀ hhalf).2
    linarith only [exp_half_lt_127_div_77]
  have hcor := reciprocal_sub_upperTailSlope_antitone (h := 1) (by norm_num)
    (show (1 / 2 : ℝ) ∈ Ioi 0 from by norm_num) hu₀ hu
  simp only [upperTailSlope, one_mul] at hcor
  rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num] at hcor
  have hnorm : Real.exp u / (Real.exp u - 1) = 1 + 1 / (Real.exp u - 1) := by
    field_simp [hden.ne']
    ring
  have hlogBound : upperTailSlope h u - Real.exp u / (Real.exp u - 1) ≤ -(27 / 50) := by
    rw [hnorm]
    linarith only [(upperTailSlope_bounds hh hu₀).2.1, hcor, hhalfBound]
  have hf := (upperTailRatio_bounds hh hu₀).1
  have hgap : upperTailGap h u ≠ 0 := by
    intro heq
    simp [upperTailRatio, heq] at hf
  have hgapDeriv := upperTailGap_logDeriv hh hu₀
  rw [(hasDerivAt_upperTailGap hh).deriv, div_eq_iff hgap] at hgapDeriv
  have hquot := (hasDerivAt_upperTailGap hh).div
    ((Real.hasDerivAt_exp u).sub_const 1) hden.ne'
  change HasDerivAt (upperTailRatio h) _ u at hquot
  calc
    deriv (upperTailRatio h) u =
        (upperTailSlope h u - Real.exp u / (Real.exp u - 1)) * upperTailRatio h u := by
      rw [hquot.deriv, hgapDeriv]
      unfold upperTailRatio
      field_simp [hden.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right hlogBound hf.le

/-- The two slopes at `d` and `d+u` give a correlated bound on the upper-coordinate
logarithmic derivative of the leading factor. -/
theorem upperTailSlope_correlated_le {h d u : ℝ} (hh : 0 < h) (hd : 4 ≤ d)
    (hu : 0 ≤ u) (hu₄ : u ≤ 4) :
    -1 / 2 + upperTailSlope h d - upperTailSlope h (d + u) / 2 ≤ -(5 / 16) := by
  have hd₀ : 0 < d := (by norm_num : (0 : ℝ) < 4).trans_le hd
  have hv₀ : 0 < d + u := add_pos_of_pos_of_nonneg hd₀ hu
  have hdv : d ≤ d + u := le_add_of_nonneg_right hu
  have hdv₄ : d + u ≤ d + 4 := add_le_add_right hu₄ d
  have hanti := reciprocal_sub_upperTailSlope_antitone hh hd₀ hv₀ hdv
  dsimp only at hanti
  have hrecip : 1 / (d + 4) ≤ 1 / (d + u) := one_div_le_one_div_of_le hv₀ hdv₄
  have hd₄ : 1 / d ≤ (1 : ℝ) / 4 := one_div_le_one_div_of_le (by norm_num) hd
  have hprod : (32 : ℝ) ≤ d * (d + 4) := by
    have h := mul_le_mul hd (add_le_add_left hd 4) (by norm_num : (0 : ℝ) ≤ 4 + 4) hd₀.le
    norm_num at h
    exact h
  have hprodInv : 1 / (d * (d + 4)) ≤ (1 : ℝ) / 32 :=
    one_div_le_one_div_of_le (by norm_num) hprod
  have heq : 1 / d - (1 / (d + 4)) / 2 = (1 / d) / 2 + 2 * (1 / (d * (d + 4))) := by
    have hsum : 0 < d + 4 := by positivity
    field_simp [hd₀.ne', hsum.ne']
    ring
  have hsplit : 1 / d - (1 / (d + 4)) / 2 ≤ 3 / 16 := by
    rw [heq]
    linarith only [hd₄, hprodInv]
  have hLv := (upperTailSlope_bounds hh hv₀).2.1
  linarith only [hanti, hrecip, hsplit, hLv,
    show upperTailSlope h (d + u) / 2 = (1 / 2) * upperTailSlope h (d + u) by ring]

end RefinedBMV.PositiveCenter
