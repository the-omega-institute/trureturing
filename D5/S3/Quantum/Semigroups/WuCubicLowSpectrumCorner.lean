import D5.S3.Quantum.Semigroups.WuCubicBoundaryCorner
import D5.S3.Quantum.Semigroups.WuCubicSharpAngularSlice
import OmegaBuild.Commands

compile_only_with_mathlib

/-! A finite rational corner enclosure for the low-spectrum Wu cubic cut. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCorner

open _root_.Matrix
open WuCubicDirectedOccupationCap (Mat)
open WuCubicRankTwoCut (cutImbalance)
open WuCubicCoupledCuts (abs_cutEvenOffset_add_abs_cutImbalance_le_one)
open WuCubicAngularCertificate (thermalCenter normalizedDeficit cutEnergy cutBias
  lowerCoeff upperCoeff longCoeff)
open WuCubicSharpAngularSlice (sharp_slice_min_le_normalizedDeficit imbalanceSliceMin
  squareSliceMin squareBoundaryMin squareEdgeMin)
open WuRepeatedMiddleCubic (alpha)
open private gamma h gibbsLow gibbsHigh cutA cutB c e bias from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private totalAt from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
open private logLower logUpper logRatioLower logRatioUpper logRatio_bounds min_div_le
  logLower_le le_logUpper logSeries logCoordinate gibbsArgument thermalBase thermalFactor from
  D5.S3.Quantum.Semigroups.WuCubicBoundaryCorner
open private crossCoeff directedCoeff from D5.S3.Quantum.Semigroups.WuCubicAngularCertificate

private def entropyLower (r m n q : ℝ) : ℝ :=
  let T := totalAt m n q
  T * (logLower (gibbsArgument r) + logLower (T / 4)) -
    m ^ 3 * logUpper (m ^ 3) - n ^ 3 * logUpper (n ^ 3) - q ^ 3 * logUpper (q ^ 3)

/-- At zero mass the corresponding entropy term vanishes. At tracial
temperature the coefficient of the entropy is exactly one half. -/
def thermalCenterLower (r m n q : ℝ) : ℝ :=
  let S := entropyLower r m n q
  thermalBase r (totalAt m n q) +
    if r = 1 then S / 2
    else thermalFactor r * min (S / logRatioLower r) (S / logRatioUpper r)

private theorem mul_logUpper {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x * Real.log x ≤ x * logUpper x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · exact mul_le_mul_of_nonneg_left (le_logUpper hx hx1) hx.le

/-- The rational thermal enclosure applies to every ordered spectrum in
`[0,1]`, including a zero lowest level. -/
theorem thermalCenterLower_le {r m n q : ℝ} (hr : 1 ≤ r)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq1 : q ≤ 1) :
    thermalCenterLower r m n q ≤ thermalCenter r m n q := by
  let T := totalAt m n q
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hn := hm.trans hmn
  have hq := hn.trans hnq
  have hT : 0 < T := by unfold T totalAt; positivity
  have cube_le_one {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : x ^ 3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hx hx1 3
  have hm3 := cube_le_one hm (hmn.trans (hnq.trans hq1))
  have hn3 := cube_le_one hn (hnq.trans hq1)
  have hq3 := cube_le_one hq hq1
  have hT4 : T / 4 ≤ 1 := by
    unfold T totalAt
    linarith only [hm3, hn3, hq3]
  have hg : 0 < gibbsArgument r := by unfold gibbsArgument gibbsHigh gibbsLow; positivity
  have hg1 : gibbsArgument r ≤ 1 := by
    have hd : 0 < 1 + r ^ 3 := by positivity
    have harg : gibbsArgument r = 4 * r ^ 3 / (1 + r ^ 3) ^ 2 := by
      unfold gibbsArgument gibbsHigh gibbsLow
      field_simp [hd.ne']
    rw [harg, div_le_iff₀ (sq_pos_of_pos hd)]
    nlinarith only [sq_nonneg (r ^ 3 - 1)]
  let S := T * (Real.log (gibbsArgument r) + Real.log (T / 4)) -
    m ^ 3 * Real.log (m ^ 3) - n ^ 3 * Real.log (n ^ 3) - q ^ 3 * Real.log (q ^ 3)
  have hS : entropyLower r m n q ≤ S := by
    unfold entropyLower S
    exact sub_le_sub
      (sub_le_sub
        (sub_le_sub
          (mul_le_mul_of_nonneg_left
            (add_le_add (logLower_le hg hg1) (logLower_le (by positivity) hT4)) hT.le)
          (mul_logUpper (by positivity) hm3))
        (mul_logUpper (by positivity) hn3))
      (mul_logUpper (by positivity) hq3)
  have hcenter : thermalCenter r m n q = thermalBase r T + alpha r * S := by
    unfold thermalCenter h thermalBase S gibbsArgument
    change _ = _ * T + _
    ring
  rw [hcenter, thermalCenterLower]
  by_cases hr1 : r = 1
  · rw [if_pos hr1, alpha, if_pos hr1]
    linarith only [hS]
  · rw [if_neg hr1]
    have hr' := lt_of_le_of_ne hr (Ne.symm hr1)
    obtain ⟨hlo, hdlo, hdhi⟩ := logRatio_bounds hr'
    have hfactor : 0 ≤ thermalFactor r := by
      unfold thermalFactor
      have hnum : 0 ≤ r ^ 2 - 1 := sub_nonneg.mpr (by
        simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hr 2)
      positivity
    have halpha : alpha r = thermalFactor r / Real.log r := by
      simp only [alpha, if_neg hr1, thermalFactor, div_div]
    rw [halpha, show thermalFactor r / Real.log r * S =
      thermalFactor r * (S / Real.log r) by ring]
    exact add_le_add_left (mul_le_mul_of_nonneg_left (min_div_le hS hlo hdlo hdhi) hfactor) _

/-- At a rational corner, the thermal bracket, clipped imbalance minimum and
square minimum use only finite rational arithmetic. The weights `L` and `R`
mix the signed and local adjacent-cut bounds. The charges `μ₀` and `μ₂` retain
the partner-mass corrections at the singleton cuts. -/
def cornerLower (r m n q L R μ₀ μ₂ : ℝ) : ℝ :=
  let A := cutEnergy r m n q
  let B := cutBias r m n q
  let Z₀ := lowerCoeff r m n q
  let Z₂ := upperCoeff r n q
  let κ := longCoeff r m n q / 4
  let H := A 1 + (L + R) / 2
  let K := 2 * A 1 + H
  let C := A 1 + (Z₀ + Z₂) / 2 + (3 * (A 0 + A 2) - B 0 - B 2) / 2
  let g := μ₀ - μ₂
  let I := if K = 0 then 0 else 1 / (4 * K)
  let loss := if K = 0 then |g| else I * g ^ 2
  thermalCenterLower r m n q +
    (C - loss + imbalanceSliceMin H (B 1 + μ₀ + μ₂) 0 1 +
      squareSliceMin ((A 0 + Z₀ - L) / 2 + κ - I * L ^ 2)
        ((A 2 + Z₂ - R) / 2 + κ - I * R ^ 2)
        (2 * (I * L * R - κ)) (B 0 / 2 - μ₀ - 2 * I * L * g)
        (B 2 / 2 - μ₂ + 2 * I * R * g))

/-- Exact corner lower bound for arbitrary complex unitary frames. -/
theorem cornerLower_le_normalizedDeficit {r m n q L R μ₀ μ₂ : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq1 : q ≤ 1)
    (hL : L ∈ Set.Icc 0 (lowerCoeff r m n q)) (hR : R ∈ Set.Icc 0 (upperCoeff r n q))
    (hμ₀ : μ₀ ∈ Set.Icc 0 (cutBias r m n q 0)) (hμ₂ : μ₂ ∈ Set.Icc 0 (cutBias r m n q 2)) :
    cornerLower r m n q L R μ₀ μ₂ ≤ normalizedDeficit r U m n q := by
  have hv : |cutImbalance U| ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨abs_nonneg _, (le_add_of_nonneg_left (abs_nonneg _)).trans
      (abs_cutEvenOffset_add_abs_cutImbalance_le_one U)⟩
  have hcuts := sharp_slice_min_le_normalizedDeficit U hr hm hmn hnq hq1 le_rfl
    (by norm_num) hv hL hR hμ₀ hμ₂
  unfold cornerLower
  refine (add_le_add_right (thermalCenterLower_le hr hm hmn hnq hq1) _).trans ?_
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_div, add_zero, one_mul]
    using hcuts

/-- At this low-spectrum shell corner, half of each signed adjacent-cut
estimate already certifies a uniform positive normalized deficit. -/
theorem shellCorner_normalizedDeficit (U : unitary Mat) :
    (7 / 1000 : ℝ) ≤ normalizedDeficit (6 / 5) U (63 / 100) (3 / 4) (9 / 10) := by
  let r : ℝ := 6 / 5
  let m : ℝ := 63 / 100
  let n : ℝ := 3 / 4
  let q : ℝ := 9 / 10
  let L := lowerCoeff r m n q / 2
  let R := upperCoeff r n q / 2
  have hL : L ∈ Set.Icc 0 (lowerCoeff r m n q) := by
    norm_num [L, r, m, n, q, lowerCoeff, crossCoeff, directedCoeff, c, e, gamma]
  have hR : R ∈ Set.Icc 0 (upperCoeff r n q) := by
    norm_num [R, r, n, q, upperCoeff, crossCoeff, directedCoeff, c, e, gamma]
  have hcharges : (0 : ℝ) ∈ Set.Icc 0 (cutBias r m n q 0) ∧
      (0 : ℝ) ∈ Set.Icc 0 (cutBias r m n q 2) := by
    norm_num [r, m, n, q, cutBias, cutB, bias, e, gamma]
  have hmargin : (7 / 1000 : ℝ) ≤ cornerLower r m n q L R 0 0 := by
    norm_num [r, m, n, q, L, R, cornerLower, thermalCenterLower, entropyLower, thermalBase,
      thermalFactor, gibbsArgument, gibbsLow, gibbsHigh, totalAt, logLower, logUpper,
      logRatioLower, logRatioUpper, logSeries, logCoordinate, Finset.sum_range_succ,
      cutEnergy, cutBias, cutA, cutB, lowerCoeff, upperCoeff, longCoeff, crossCoeff,
      directedCoeff, c, e, bias, gamma, imbalanceSliceMin, squareSliceMin, squareBoundaryMin,
      squareEdgeMin, min_def, abs_def]
  exact hmargin.trans (cornerLower_le_normalizedDeficit U (by norm_num [r]) (by norm_num [m])
    (by norm_num [m, n]) (by norm_num [n, q]) (by norm_num [q]) hL hR hcharges.1 hcharges.2)

#print axioms cornerLower_le_normalizedDeficit
#print axioms shellCorner_normalizedDeficit

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCorner
