import D5.S3.Quantum.Semigroups.WuCubicBoundaryThermal
import D5.S3.Quantum.Semigroups.WuCubicCornerInterpolation
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCorner
import OmegaBuild.Commands

/-! Thermal interpolation of the normalized Wu cubic deficit at fixed spectrum. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrumThermalInterpolation

open _root_.Matrix Set
open scoped Topology

open WuCubicDirectedOccupationCap (Mat)
open WuRepeatedMiddleCubic (alpha)
open WuCubicAngularCertificate (normalizedDeficit cutEnergy cutBias lowerCoeff upperCoeff longCoeff)
open WuCubicBoundaryThermal (jumpContribution spectralCharge normalizedDeficit_eq_jumpContribution
  normalizedDeficit_second_le)
open WuCubicCornerInterpolation (corner_interpolation)
open WuCubicLowSpectrumCorner
  (cornerLower thermalCenterLower cornerLower_le_normalizedDeficit shellCorner_normalizedDeficit)
open WuCubicSharpAngularSlice (imbalanceSliceMin squareSliceMin squareBoundaryMin squareEdgeMin)

open private gamma h gibbsLow gibbsHigh cutA cutB c e bias from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private totalAt from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
open private centeredEntropy h_hasDerivAt alpha_hasDerivAt bias_hasDerivAt
  jumpContribution_hasDerivAt h_second_hasDerivAt alpha_second_hasDerivAt
  bias_second_hasDerivAt jumpContribution_second_hasDerivAt from
  D5.S3.Quantum.Semigroups.WuCubicBoundaryThermal
open private logUpper logRatioLower logRatioUpper logSeries logCoordinate gibbsArgument
  thermalBase thermalFactor from D5.S3.Quantum.Semigroups.WuCubicBoundaryCorner
open private entropyLower massLogUpper logLower from
  D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCorner
open private crossCoeff directedCoeff from D5.S3.Quantum.Semigroups.WuCubicAngularCertificate

private theorem normalizedDeficit_thermal_differentiable (U : unitary Mat) {m n q r : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hq : 0 ≤ q) (hr : 1 < r) :
    DifferentiableAt ℝ (fun y => normalizedDeficit y U m n q) r ∧
      DifferentiableAt ℝ (deriv (fun y => normalizedDeficit y U m n q)) r := by
  let T := totalAt m n q
  let Q := centeredEntropy (m ^ 3) (n ^ 3) (q ^ 3)
  let J := jumpContribution U m n q
  let C := spectralCharge U m n q
  let F := fun y => h y * T + alpha y * Q + J y + bias y * C
  have heq : (fun y => normalizedDeficit y U m n q) =ᶠ[𝓝 r] F := by
    filter_upwards [lt_mem_nhds hr] with y hy
    exact normalizedDeficit_eq_jumpContribution U hy.le hm hn hq
  let F₁ := fun y => deriv h y * T + deriv alpha y * Q + deriv J y + deriv bias y * C
  have hF (y : ℝ) (hy : 1 < y) : HasDerivAt F (F₁ y) y := by
    have hy₀ := zero_lt_one.trans hy
    have hh := h_hasDerivAt hy
    have ha := alpha_hasDerivAt hy
    have hb := bias_hasDerivAt hy₀
    exact ((((hh.congr_deriv hh.deriv.symm).mul_const T).fun_add
      ((ha.congr_deriv ha.deriv.symm).mul_const Q)).fun_add
      (jumpContribution_hasDerivAt U m n q hy₀)).fun_add
      ((hb.congr_deriv hb.deriv.symm).mul_const C)
  refine ⟨(hF r hr).differentiableAt.congr_of_eventuallyEq heq, ?_⟩
  have hfirst : deriv F =ᶠ[𝓝 r] F₁ := by
    filter_upwards [lt_mem_nhds hr] with y hy
    exact (hF y hy).deriv
  have hr₀ := zero_lt_one.trans hr
  have hdiff : DifferentiableAt ℝ F₁ r :=
    ((((h_second_hasDerivAt hr).mul_const T).fun_add
      ((alpha_second_hasDerivAt hr).mul_const Q)).fun_add
      (jumpContribution_second_hasDerivAt U m n q hr₀)).fun_add
      ((bias_second_hasDerivAt hr₀).mul_const C) |>.differentiableAt
  exact hdiff.congr_of_eventuallyEq (heq.deriv.trans hfirst)

/-- The fixed-spectrum deficit lies above its thermal chord after the
quadratic correction from the uniform curvature bound. -/
theorem normalizedDeficit_thermal_chord (U : unitary Mat) {m n q lo hi r : ℝ}
    (hm : m ∈ Ioc (0 : ℝ) 1) (hn : n ∈ Ioc (0 : ℝ) 1) (hq : q ∈ Ioc (0 : ℝ) 1)
    (hlo : 1 < lo) (hlt : lo < hi) (hhi : hi ≤ 6 / 5) (hr : r ∈ Icc lo hi) :
    ((hi - r) / (hi - lo)) * normalizedDeficit lo U m n q +
        ((r - lo) / (hi - lo)) * normalizedDeficit hi U m n q -
        40 * (r - lo) * (hi - r) ≤ normalizedDeficit r U m n q := by
  let f := fun t => normalizedDeficit t U m n q
  have hdiff (t : ℝ) (ht : lo ≤ t) :
      DifferentiableAt ℝ f t ∧ DifferentiableAt ℝ (deriv f) t :=
    normalizedDeficit_thermal_differentiable U hm.1.le hn.1.le hq.1.le (hlo.trans_le ht)
  let l := min m (min n q)
  have hl : 0 < l := lt_min hm.1 (lt_min hn.1 hq.1)
  have hlm : l ≤ m := min_le_left _ _
  have hln : l ≤ n := (min_le_right _ _).trans (min_le_left _ _)
  have hlq : l ≤ q := (min_le_right _ _).trans (min_le_right _ _)
  have hmass : 0 < totalAt m n q := by
    unfold totalAt
    linarith only [pow_nonneg hm.1.le 3, pow_nonneg hn.1.le 3, pow_nonneg hq.1.le 3]
  have hcurvature (t : ℝ) (ht : t ∈ Ioo lo hi) : deriv^[2] f t ≤ 80 := by
    have hbound := normalizedDeficit_second_le U hl ⟨hlm, hm.2⟩ ⟨hln, hn.2⟩ ⟨hlq, hq.2⟩
      (hlo.trans ht.1) (ht.2.le.trans hhi) hmass le_rfl le_rfl
    simpa only [f, Function.iterate_succ_apply, Function.iterate_zero_apply] using
      hbound.trans (min_le_left _ _)
  have hchord := corner_interpolation (f := f) 80 lo hi r hlt
    (fun t ht => (hdiff t ht.1).1.continuousAt.continuousWithinAt)
    (fun t ht => (hdiff t ht.1.le).1.differentiableWithinAt)
    (fun t ht => (hdiff t ht.1.le).2.differentiableWithinAt) hcurvature hr.1 hr.2
  simpa only [f, show (80 : ℝ) / 2 = 40 by norm_num] using hchord

private theorem shellLeft_normalizedDeficit (U : unitary Mat) :
    (3 / 400 : ℝ) ≤ normalizedDeficit (1199 / 1000) U (63 / 100) (3 / 4) (9 / 10) := by
  let r : ℝ := 1199 / 1000
  let m : ℝ := 63 / 100
  let n : ℝ := 3 / 4
  let q : ℝ := 9 / 10
  let L := lowerCoeff r m n q / 2
  let R := upperCoeff r n q / 2
  have hL : L ∈ Icc 0 (lowerCoeff r m n q) := by
    norm_num [L, r, m, n, q, lowerCoeff, crossCoeff, directedCoeff, c, e, gamma]
  have hR : R ∈ Icc 0 (upperCoeff r n q) := by
    norm_num [R, r, n, q, upperCoeff, crossCoeff, directedCoeff, c, e, gamma]
  have hcharges : (0 : ℝ) ∈ Icc 0 (cutBias r m n q 0) ∧
      (0 : ℝ) ∈ Icc 0 (cutBias r m n q 2) := by
    norm_num [r, m, n, q, cutBias, cutB, bias, e, gamma]
  have hmargin : (3 / 400 : ℝ) ≤ cornerLower r m n q L R 0 0 := by
    norm_num [r, m, n, q, L, R, cornerLower, thermalCenterLower, entropyLower, massLogUpper,
      thermalBase, thermalFactor, gibbsArgument, gibbsLow, gibbsHigh, totalAt, logLower, logUpper,
      logRatioLower, logRatioUpper, logSeries, logCoordinate, Finset.sum_range_succ,
      cutEnergy, cutBias, cutA, cutB, lowerCoeff, upperCoeff, longCoeff, crossCoeff,
      directedCoeff, c, e, bias, gamma, imbalanceSliceMin, squareSliceMin, squareBoundaryMin,
      squareEdgeMin, min_def]
  exact hmargin.trans (cornerLower_le_normalizedDeficit U (by norm_num [r]) (by norm_num [m])
    (by norm_num [m, n]) (by norm_num [n, q]) (by norm_num [q]) hL hR hcharges.1 hcharges.2)

/-- The left corner surplus pays the full chord correction on the shell
interval, preserving the right corner's positive margin. -/
theorem shellThermalInterval_normalizedDeficit (U : unitary Mat) {r : ℝ}
    (hr : r ∈ Icc (1199 / 1000 : ℝ) (6 / 5)) :
    (7 / 1000 : ℝ) ≤ normalizedDeficit r U (63 / 100) (3 / 4) (9 / 10) := by
  let lo : ℝ := 1199 / 1000
  let hi : ℝ := 6 / 5
  let a := (hi - r) / (hi - lo)
  let b := (r - lo) / (hi - lo)
  have hw : 0 ≤ hi - lo := by norm_num [hi, lo]
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hr.2) hw
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hr.1) hw
  have hchord := normalizedDeficit_thermal_chord U (m := 63 / 100) (n := 3 / 4) (q := 9 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl hr
  have hlinear := add_le_add (mul_le_mul_of_nonneg_left (shellLeft_normalizedDeficit U) ha)
    (mul_le_mul_of_nonneg_left (shellCorner_normalizedDeficit U) hb)
  have hmargin : (7 / 1000 : ℝ) ≤ a * (3 / 400) + b * (7 / 1000) -
      40 * (r - lo) * (hi - r) := by
    have hspan : 0 ≤ hi - r := sub_nonneg.mpr hr.2
    calc
      (7 / 1000 : ℝ) ≤ 7 / 1000 + ((23 / 50) * (hi - r) + 40 * (hi - r) ^ 2) :=
        le_add_of_nonneg_right (add_nonneg (mul_nonneg (by norm_num) hspan)
          (mul_nonneg (by norm_num) (sq_nonneg _)))
      _ = _ := by
        dsimp only [a, b, lo, hi]
        ring
  exact hmargin.trans ((sub_le_sub_right hlinear _).trans hchord)

#print axioms normalizedDeficit_thermal_chord
#print axioms shellThermalInterval_normalizedDeficit

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrumThermalInterpolation
