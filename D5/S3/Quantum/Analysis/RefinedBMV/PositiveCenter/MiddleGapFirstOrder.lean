/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleGapFirstOrder
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Slope and curvature bounds for the first-order middle-gap profile. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapSign

/-! # First-order middle-gap bounds for the refined BMV kernel -/

open Filter
open scoped Topology

namespace RefinedBMV.PositiveCenter

private noncomputable def firstOrderCoeff (h : ℝ) : ℝ := (3 + h) * (3 + 2 * h) / 2

private noncomputable def firstOrderRate (h : ℝ) : ℝ := 3 / 2 + h

/-- The first-order expansion of the middle-gap profile. -/
noncomputable def middleGapFirstOrder (h t : ℝ) : ℝ :=
  firstOrderCoeff h / 2 * upperTailGap h t * Real.exp (-(1 / 2 * t)) +
    1 / 2 * Real.exp (-(firstOrderRate h * t)) * (3 + h - 1 / upperTailGap h t)

private theorem firstOrder_gap_reciprocal {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    1 / upperTailGap h t = h + upperTailSlope h t := by
  have ha : 0 < upperTailGap h t := by
    rw [expGapMean_eq hh]
    exact mul_pos ht (expGapMean_pos _ _)
  have hgap : h * upperTailGap h t + Real.exp (-(h * t)) = 1 := by
    unfold upperTailGap
    field_simp [hh.ne']
    ring
  rw [← upperTailGap_logDeriv hh ht, (hasDerivAt_upperTailGap hh).deriv]
  field_simp [ha.ne']
  linarith only [hgap]

private theorem hasDerivAt_firstOrder_exp (k t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.exp (-(k * x))) (-k * Real.exp (-(k * t))) t := by
  simpa [mul_comm] using ((hasDerivAt_id' t).const_mul k).neg.exp

private theorem deriv_middleGapFirstOrder {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    let c := firstOrderCoeff h
    let m := firstOrderRate h
    let a := upperTailGap h t
    let s := upperTailSlope h t
    deriv (middleGapFirstOrder h) t =
      c / 2 * (Real.exp (-(h * t)) - a / 2) * Real.exp (-(1 / 2 * t)) +
        1 / 2 * Real.exp (-(m * t)) * ((m + s) * (h + s) - m * (3 + h)) := by
  let c := firstOrderCoeff h
  let m := firstOrderRate h
  dsimp only
  have heq : middleGapFirstOrder h =ᶠ[𝓝 t] (fun x ↦
      c / 2 * upperTailGap h x * Real.exp (-(1 / 2 * x)) +
        1 / 2 * Real.exp (-(m * x)) * (3 + h - (h + upperTailSlope h x))) := by
    filter_upwards [eventually_gt_nhds ht] with x hx
    unfold middleGapFirstOrder
    rw [firstOrder_gap_reciprocal hh hx]
  have ha := hasDerivAt_upperTailGap (t := t) hh
  have hs := hasDerivAt_upperTailSlope hh ht
  have hmain := (ha.const_mul (c / 2)).mul (hasDerivAt_firstOrder_exp (1 / 2) t)
  have hrest := ((hasDerivAt_firstOrder_exp m t).const_mul (1 / 2)).mul
    ((hs.const_add h).const_sub (3 + h))
  have hd := hmain.add hrest
  change HasDerivAt (fun x ↦
      c / 2 * upperTailGap h x * Real.exp (-(1 / 2 * x)) +
        1 / 2 * Real.exp (-(m * x)) * (3 + h - (h + upperTailSlope h x))) _ t at hd
  rw [heq.deriv_eq, hd.deriv]
  ring

private theorem deriv_deriv_middleGapFirstOrder {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    let c := firstOrderCoeff h
    let m := firstOrderRate h
    let a := upperTailGap h t
    let s := upperTailSlope h t
    deriv (deriv (middleGapFirstOrder h)) t =
      c / 2 * (a / 4 - (1 + h) * Real.exp (-(h * t))) * Real.exp (-(1 / 2 * t)) +
        1 / 2 * Real.exp (-(m * t)) *
          (m ^ 2 * (3 + h) - (h + s) * (m ^ 2 + (2 * m + h) * s + 2 * s ^ 2)) := by
  let c := firstOrderCoeff h
  let m := firstOrderRate h
  dsimp only
  have heq : deriv (middleGapFirstOrder h) =ᶠ[𝓝 t] (fun x ↦
      c / 2 * (Real.exp (-(h * x)) - upperTailGap h x / 2) * Real.exp (-(1 / 2 * x)) +
        1 / 2 * Real.exp (-(m * x)) *
          ((m + upperTailSlope h x) * (h + upperTailSlope h x) - m * (3 + h))) := by
    filter_upwards [eventually_gt_nhds ht] with x hx
    exact deriv_middleGapFirstOrder hh hx
  have ha := hasDerivAt_upperTailGap (t := t) hh
  have hs := hasDerivAt_upperTailSlope hh ht
  have hmain := (((hasDerivAt_firstOrder_exp h t).sub (ha.div_const 2)).const_mul
    (c / 2)).mul (hasDerivAt_firstOrder_exp (1 / 2) t)
  have hrest := ((hasDerivAt_firstOrder_exp m t).const_mul (1 / 2)).mul
    (((hs.const_add m).mul (hs.const_add h)).sub_const (m * (3 + h)))
  have hd := hmain.add hrest
  change HasDerivAt (fun x ↦
      c / 2 * (Real.exp (-(h * x)) - upperTailGap h x / 2) * Real.exp (-(1 / 2 * x)) +
        1 / 2 * Real.exp (-(m * x)) *
          ((m + upperTailSlope h x) * (h + upperTailSlope h x) - m * (3 + h))) _ t at hd
  rw [heq.deriv_eq, hd.deriv]
  simp only [Pi.sub_apply, Pi.mul_apply]
  ring

private theorem firstOrder_gap_lower {h t : ℝ} (hh : 0 < h) (ht : 0 ≤ t) :
    (t + h * t ^ 2 / 2) * Real.exp (-(h * t)) ≤ upperTailGap h t := by
  have hTaylor := Real.quadratic_le_exp_of_nonneg (mul_nonneg hh.le ht)
  have hbound : t + h * t ^ 2 / 2 ≤ (Real.exp (h * t) - 1) / h := by
    apply (le_div_iff₀ hh).2
    nlinarith only [hTaylor]
  calc
    _ ≤ (Real.exp (h * t) - 1) / h * Real.exp (-(h * t)) :=
      mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le
    _ = _ := by
      rw [upperTailGap, Real.exp_neg]
      field_simp [hh.ne', (Real.exp_pos (h * t)).ne']

private theorem firstOrder_slope_le_quarter {h t : ℝ} (hh : 0 < h) (ht : 4 ≤ t) :
    upperTailSlope h t ≤ 1 / 4 :=
  (upperTailSlope_bounds hh (by linarith)).2.1.trans
    (one_div_le_one_div_of_le (by norm_num) ht)

private theorem firstOrder_coeff_lower {h : ℝ} (hh : 0 < h) :
    9 / 4 ≤ firstOrderCoeff h / 2 := by
  unfold firstOrderCoeff
  nlinarith only [hh, sq_nonneg h]

private theorem middleGapSlopeBudget_le_firstOrder_main {h t : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3 / 11) (ht : 4 ≤ t) :
    middleGapSlopeBudget h t ≤
      9 / 4 * (t / 2 - 1) * Real.exp (-(h * t)) * Real.exp (-(1 / 2 * t)) := by
  let m := firstOrderRate h
  have ht₀ : 0 ≤ t := by linarith
  have ha₀ : 0 ≤ upperTailGap h t := by
    rw [expGapMean_eq hh]
    exact mul_nonneg ht₀ (expGapMean_pos _ _).le
  have hrecip : 1 / (4 + t) ≤ (1 / 8 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hm : m + 1 / (4 + t) ≤ 2 := by
    dsimp [m, firstOrderRate]
    linarith only [hhmax, hrecip]
  have hm₀ : 0 ≤ m + 1 / (4 + t) := by
    dsimp [m, firstOrderRate]
    positivity
  have hbudget : middleGapSlopeBudget h t ≤
      6 * (1 + t / 4) * Real.exp (-(3 * t / 2)) := by
    unfold middleGapSlopeBudget
    have hcoeff : (11 / 4 + 1 / 25000) * (m + 1 / (4 + t)) ≤ 6 := by
      calc
        _ ≤ (3 : ℝ) * 2 := mul_le_mul (by norm_num) hm hm₀ (by norm_num)
        _ = _ := by norm_num
    have hgap : 1 + upperTailGap h t / 4 ≤ 1 + t / 4 := by
      linarith only [upperTailGap_le (t := t) hh]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hcoeff hgap (by positivity) (by norm_num)) (Real.exp_pos _).le
  have hexp₀ : (6 : ℝ) ≤ 9 / 8 * Real.exp (8 / 11 * t) := by
    have hexp := (Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 32 / 11)).trans
      (Real.exp_le_exp.mpr (show 32 / 11 ≤ 8 / 11 * t by linarith only [ht]))
    linarith only [hexp]
  have hexps :
      Real.exp (8 / 11 * t) * Real.exp (-(3 * t / 2)) ≤
        Real.exp (-(h * t)) * Real.exp (-(1 / 2 * t)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right hhmax ht₀])
  calc
    _ ≤ 6 * (1 + t / 4) * Real.exp (-(3 * t / 2)) := hbudget
    _ ≤ (9 / 8 * (1 + t / 4)) * (Real.exp (8 / 11 * t) * Real.exp (-(3 * t / 2))) := by
      calc
        _ ≤ (9 / 8 * Real.exp (8 / 11 * t)) * (1 + t / 4) * Real.exp (-(3 * t / 2)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp₀ (by positivity))
            (Real.exp_pos _).le
        _ = _ := by ring
    _ ≤ (9 / 4 * (t / 2 - 1)) * (Real.exp (-(h * t)) * Real.exp (-(1 / 2 * t))) := by
      have hratio : (9 / 8 : ℝ) * (1 + t / 4) ≤ 9 / 4 * (t / 2 - 1) := by linarith only [ht]
      have hratio₀ : 0 ≤ (9 / 8 : ℝ) * (1 + t / 4) := by positivity
      exact mul_le_mul hratio hexps (by positivity) (hratio₀.trans hratio)
    _ = _ := by ring

/-- The negative slope of the first-order profile supplies the middle-gap slope budget. -/
theorem middleGapSlopeBudget_le_neg_deriv_middleGapFirstOrder {h t : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3 / 11) (ht : 4 ≤ t) :
    middleGapSlopeBudget h t ≤ -deriv (middleGapFirstOrder h) t := by
  let m := firstOrderRate h
  let s := upperTailSlope h t
  let a := upperTailGap h t
  have ht₀ : 0 < t := by linarith
  have hs := (upperTailSlope_bounds hh ht₀).1
  have hsmax := firstOrder_slope_le_quarter hh ht
  have hm₀ : 3 / 2 ≤ m := by dsimp [m, firstOrderRate]; linarith only [hh]
  have hmmax : m ≤ 2 := by dsimp [m, firstOrderRate]; linarith only [hhmax]
  have hrest : 0 ≤ m * (3 + h) - (m + s) * (h + s) := by
    have hmg : (3 / 2 : ℝ) * 3 ≤ m * (3 + h) :=
      mul_le_mul hm₀ (by linarith only [hh]) (by norm_num) (by positivity)
    have hms : (m + s) * (h + s) ≤ (9 / 4 : ℝ) * 1 :=
      mul_le_mul (by linarith only [hmmax, hsmax]) (by linarith only [hhmax, hsmax])
        (by positivity) (by norm_num)
    linarith only [hmg, hms]
  have ha : t * Real.exp (-(h * t)) ≤ a :=
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity : 0 ≤ h * t ^ 2 / 2))
      (Real.exp_pos _).le).trans (firstOrder_gap_lower hh ht₀.le)
  have hmain : (t / 2 - 1) * Real.exp (-(h * t)) ≤ a / 2 - Real.exp (-(h * t)) := by
    linarith only [ha]
  have hmain₀ : 0 ≤ (t / 2 - 1) * Real.exp (-(h * t)) :=
    mul_nonneg (by linarith only [ht]) (Real.exp_pos _).le
  have hcoeff := firstOrder_coeff_lower hh
  calc
    _ ≤ 9 / 4 * (t / 2 - 1) * Real.exp (-(h * t)) * Real.exp (-(1 / 2 * t)) :=
      middleGapSlopeBudget_le_firstOrder_main hh hhmax ht
    _ ≤ firstOrderCoeff h / 2 * (a / 2 - Real.exp (-(h * t))) * Real.exp (-(1 / 2 * t)) := by
      rw [mul_assoc (9 / 4 : ℝ) (t / 2 - 1)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hcoeff hmain hmain₀ ((by norm_num : (0 : ℝ) ≤ 9 / 4).trans hcoeff))
        (Real.exp_pos _).le
    _ ≤ _ := by
      rw [deriv_middleGapFirstOrder hh ht₀]
      change _ ≤ -(firstOrderCoeff h / 2 * (Real.exp (-(h * t)) - a / 2) *
        Real.exp (-(1 / 2 * t)) + 1 / 2 * Real.exp (-(m * t)) *
          ((m + s) * (h + s) - m * (3 + h)))
      have h := mul_nonneg (by positivity : 0 ≤ 1 / 2 * Real.exp (-(m * t))) hrest
      linarith only [h]

/-- The first-order profile is strictly convex throughout the analytic middle-gap region. -/
theorem deriv_deriv_middleGapFirstOrder_pos {h t : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3 / 11) (ht : 4 ≤ t) :
    0 < deriv (deriv (middleGapFirstOrder h)) t := by
  let m := firstOrderRate h
  let s := upperTailSlope h t
  let a := upperTailGap h t
  have ht₀ : 0 < t := by linarith
  have hs : 0 < s := (upperTailSlope_bounds hh ht₀).1
  have hsmax : s ≤ 1 / 4 := firstOrder_slope_le_quarter hh ht
  have hm₀ : 3 / 2 ≤ m := by dsimp [m, firstOrderRate]; linarith only [hh]
  have hmmax : m ≤ 2 := by dsimp [m, firstOrderRate]; linarith only [hhmax]
  have hB : 0 < m ^ 2 * (3 + h) - (h + s) * (m ^ 2 + (2 * m + h) * s + 2 * s ^ 2) := by
    have hm_sq_low : (3 / 2 : ℝ) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by norm_num) hm₀ 2
    have hm_sq_high : m ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (by linarith only [hm₀]) hmmax 2
    have hmg : (3 / 2 : ℝ) ^ 2 * 3 ≤ m ^ 2 * (3 + h) :=
      mul_le_mul hm_sq_low (by linarith only [hh]) (by norm_num) (sq_nonneg _)
    have hms : (2 * m + h) * s ≤ (5 : ℝ) * (1 / 4) :=
      mul_le_mul (by linarith only [hmmax, hhmax]) hsmax hs.le (by norm_num)
    have hs_sq : s ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ hs.le hsmax 2
    have hbracket : m ^ 2 + (2 * m + h) * s + 2 * s ^ 2 ≤ 6 := by
      linarith only [hm_sq_high, hms, hs_sq]
    have hprod : (h + s) * (m ^ 2 + (2 * m + h) * s + 2 * s ^ 2) ≤ (1 : ℝ) * 6 := by
      have hmpos : 0 < m := by linarith only [hm₀]
      exact mul_le_mul (by linarith only [hhmax, hsmax]) hbracket (by positivity) zero_le_one
    linarith only [hmg, hprod]
  have hcoef : 4 * (1 + h) ≤ t + h * t ^ 2 / 2 := by
    have ht_sq : 8 ≤ t ^ 2 := by nlinarith only [ht, sq_nonneg (t - 4)]
    linarith only [ht, mul_le_mul_of_nonneg_left ht_sq hh.le]
  have hgap : 0 ≤ a / 4 - (1 + h) * Real.exp (-(h * t)) := by
    have ha := (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos (-(h * t))).le).trans
      (firstOrder_gap_lower hh ht₀.le)
    linarith only [ha]
  rw [deriv_deriv_middleGapFirstOrder hh ht₀]
  change 0 < firstOrderCoeff h / 2 * (a / 4 - (1 + h) * Real.exp (-(h * t))) *
    Real.exp (-(1 / 2 * t)) + 1 / 2 * Real.exp (-(m * t)) *
      (m ^ 2 * (3 + h) - (h + s) * (m ^ 2 + (2 * m + h) * s + 2 * s ^ 2))
  have hc := (by norm_num : (0 : ℝ) ≤ 9 / 4).trans (firstOrder_coeff_lower hh)
  exact add_pos_of_nonneg_of_pos (mul_nonneg (mul_nonneg hc hgap) (Real.exp_pos _).le)
    (mul_pos (by positivity) hB)

#print axioms middleGapSlopeBudget_le_neg_deriv_middleGapFirstOrder
#print axioms deriv_deriv_middleGapFirstOrder_pos

end RefinedBMV.PositiveCenter
