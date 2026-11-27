import D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
import Batteries.Tactic.OpenPrivate

/-! A rational thermal-center enclosure for Wu v1, Remark 3.15 (3.54). -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Semigroups.WuCubicBoundaryCorner

open WuCubicAngularCertificate (thermalCenter)
open WuRepeatedMiddleCubic (alpha)
open private gamma h gibbsLow gibbsHigh from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private totalAt from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
open private log_lower log_upper from D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap

private def logCoordinate (x : ℝ) : ℝ := (x - 1) / (x + 1)

private def logSeries (k : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, z ^ (2 * j + 1) / (2 * j + 1)

-- The coordinate is nonpositive for the Gibbs, total, and mass arguments.
private def logLower (x : ℝ) : ℝ :=
  let z := logCoordinate x
  2 * (logSeries 5 z + z ^ 11 / (1 - z ^ 2))

private def logUpper (x : ℝ) : ℝ :=
  let z := logCoordinate x
  2 * (logSeries 8 z - z ^ 17 / (1 - z ^ 2))

private def logRatioLower (r : ℝ) : ℝ := 2 * logSeries 5 (logCoordinate r)

private def logRatioUpper (r : ℝ) : ℝ :=
  let z := logCoordinate r
  2 * (logSeries 8 z + z ^ 17 / (1 - z ^ 2))

private theorem logCoordinate_mem {x : ℝ} (hx : 0 < x) : |logCoordinate x| < 1 := by
  unfold logCoordinate
  have hd : 0 < x + 1 := by positivity
  rw [abs_lt]
  constructor
  · apply (lt_div_iff₀ hd).2
    linarith
  · apply (div_lt_iff₀ hd).2
    linarith

private theorem logCoordinate_ratio {x : ℝ} (hx : 0 < x) :
    (1 + logCoordinate x) / (1 - logCoordinate x) = x := by
  have hd : x + 1 ≠ 0 := by positivity
  unfold logCoordinate
  field_simp [hd]
  ring

private theorem logLower_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    logLower x ≤ Real.log x := by
  have hz : logCoordinate x ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx1) (by positivity)
  apply log_lower _ _ _ (logCoordinate_mem hx) (logCoordinate_ratio hx)
  rw [abs_of_nonpos hz, show (-logCoordinate x) ^ 11 = -(logCoordinate x ^ 11) by ring]
  unfold logLower logSeries
  ring_nf
  exact le_rfl

private theorem le_logUpper {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.log x ≤ logUpper x := by
  have hz : logCoordinate x ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx1) (by positivity)
  apply log_upper _ _ _ (logCoordinate_mem hx) (logCoordinate_ratio hx)
  rw [abs_of_nonpos hz, show (-logCoordinate x) ^ 17 = -(logCoordinate x ^ 17) by ring]
  unfold logUpper logSeries
  ring_nf
  exact le_rfl

private theorem logRatio_bounds {r : ℝ} (hr : 1 < r) :
    0 < logRatioLower r ∧ logRatioLower r ≤ Real.log r ∧ Real.log r ≤ logRatioUpper r := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hz : 0 < logCoordinate r := div_pos (sub_pos.mpr hr) (by positivity)
  have hcoord := logCoordinate_mem hr0
  have hratio := logCoordinate_ratio hr0
  refine ⟨?_, ?_, ?_⟩
  · unfold logRatioLower logSeries
    apply mul_pos (by norm_num)
    apply Finset.sum_pos'
    · intro j _
      positivity
    · exact ⟨0, by simp, by simpa using hz⟩
  · have hsum := Real.sum_range_le_log_div hz.le (lt_of_abs_lt hcoord) 5
    rw [hratio] at hsum
    unfold logRatioLower logSeries
    linarith only [hsum]
  · have htail := (abs_le.mp (Real.sum_range_sub_log_div_le hcoord 8)).2
    rw [hratio, abs_of_pos hz] at htail
    unfold logRatioUpper logSeries
    linarith only [htail]

private def gibbsArgument (r : ℝ) : ℝ := 4 * gibbsLow r * gibbsHigh r

private def thermalBase (r T : ℝ) : ℝ := gamma r * (r - 1) ^ 2 * (r + 1) * T

private def thermalFactor (r : ℝ) : ℝ := 3 * (r ^ 2 - 1) / (4 * (r ^ 2 + r + 1))

private def entropyLower (r n q : ℝ) : ℝ :=
  let m : ℝ := 2 / 3
  let T := totalAt m n q
  T * (logLower (gibbsArgument r) + logLower (T / 4)) -
    m ^ 3 * logUpper (m ^ 3) - n ^ 3 * logUpper (n ^ 3) - q ^ 3 * logUpper (q ^ 3)

/-- Rational lower enclosure with the denominator endpoint chosen by the numerator sign. -/
def thermalCenterLower (r n q : ℝ) : ℝ :=
  let S := entropyLower r n q
  thermalBase r (totalAt (2 / 3) n q) +
    thermalFactor r * min (S / logRatioLower r) (S / logRatioUpper r)

private theorem min_div_le {a b lo d hi : ℝ} (hab : a ≤ b) (hlo : 0 < lo)
    (hdlo : lo ≤ d) (hdhi : d ≤ hi) : min (a / lo) (a / hi) ≤ b / d := by
  have hd := hlo.trans_le hdlo
  apply le_trans _ (div_le_div_of_nonneg_right hab hd.le)
  by_cases ha : 0 ≤ a
  · exact (min_le_right _ _).trans (div_le_div_of_nonneg_left ha hd hdhi)
  · apply (min_le_left _ _).trans
    rw [← neg_le_neg_iff, ← neg_div, ← neg_div]
    exact div_le_div_of_nonneg_left (neg_nonneg.mpr (le_of_not_ge ha)) hlo hdlo

/-- The enclosure holds over the whole ordered middle spectrum at (m=2/3). -/
theorem thermalCenterLower_le {r n q : ℝ} (hr : 1 < r)
    (hmn : 2 / 3 ≤ n) (hnq : n ≤ q) (hq1 : q ≤ 1) :
    thermalCenterLower r n q ≤ thermalCenter r (2 / 3) n q := by
  let m : ℝ := 2 / 3
  let T := totalAt m n q
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hm : 0 < m := by norm_num [m]
  have hn := hm.trans_le hmn
  have hq := hn.trans_le hnq
  have hT : 0 < T := by unfold T totalAt; positivity
  have cube_le_one {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : x ^ 3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hx hx1 3
  have hm3 := cube_le_one hm.le (by norm_num [m])
  have hn3 := cube_le_one hn.le (hnq.trans hq1)
  have hq3 := cube_le_one hq.le hq1
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
  have hS : entropyLower r n q ≤
      T * (Real.log (gibbsArgument r) + Real.log (T / 4)) -
        m ^ 3 * Real.log (m ^ 3) - n ^ 3 * Real.log (n ^ 3) - q ^ 3 * Real.log (q ^ 3) := by
    unfold entropyLower
    exact sub_le_sub
      (sub_le_sub
        (sub_le_sub
          (mul_le_mul_of_nonneg_left
            (add_le_add (logLower_le hg hg1) (logLower_le (by positivity) hT4)) hT.le)
          (mul_le_mul_of_nonneg_left (le_logUpper (by positivity) hm3) (by positivity)))
        (mul_le_mul_of_nonneg_left (le_logUpper (by positivity) hn3) (by positivity)))
      (mul_le_mul_of_nonneg_left (le_logUpper (by positivity) hq3) (by positivity))
  obtain ⟨hlo, hdlo, hdhi⟩ := logRatio_bounds hr
  have hfactor : 0 ≤ thermalFactor r := by
    unfold thermalFactor
    have hnum : 0 ≤ r ^ 2 - 1 := sub_nonneg.mpr (by
      simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hr.le 2)
    positivity
  have halpha : alpha r = thermalFactor r / Real.log r := by
    simp only [alpha, ite_eq_right hr.ne', thermalFactor, div_div]
  calc
    thermalCenterLower r n q ≤ thermalBase r T + thermalFactor r *
        ((T * (Real.log (gibbsArgument r) + Real.log (T / 4)) -
          m ^ 3 * Real.log (m ^ 3) - n ^ 3 * Real.log (n ^ 3) -
          q ^ 3 * Real.log (q ^ 3)) / Real.log r) :=
      add_le_add_right (mul_le_mul_of_nonneg_left (min_div_le hS hlo hdlo hdhi) hfactor) _
    _ = thermalCenter r m n q := by
      unfold thermalCenter h thermalBase gibbsArgument
      rw [halpha]
      change _ = _ * T + _
      ring

private theorem literal_thermalCenterLower :
    -(19147 / 1000000 : ℝ) ≤ thermalCenterLower (6 / 5) (4 / 5) (9 / 10) := by
  norm_num [thermalCenterLower, entropyLower, thermalBase, thermalFactor, gibbsArgument,
    gamma, gibbsLow, gibbsHigh, totalAt, logLower, logUpper, logRatioLower, logRatioUpper,
    logSeries, logCoordinate, Finset.sum_range_succ, min_def]

/-- The literal ordered spectrum `(2/3, 4/5, 9/10, 1)` at `r = 6/5`. -/
theorem literal_thermalCenter :
    -(19147 / 1000000 : ℝ) ≤ thermalCenter (6 / 5) (2 / 3) (4 / 5) (9 / 10) :=
  literal_thermalCenterLower.trans (thermalCenterLower_le (by norm_num) (by norm_num)
    (by norm_num) (by norm_num))

open _root_.Matrix
open WuCubicDirectedOccupationCap (Mat oddProbability)
open WuCubicAngularCertificate (normalizedDeficit matched_deficit_bound cutEnergy cutBias
  lowerCoeff upperCoeff longCoeff matchedMixture occupationCost longFactor tiltSum tiltDiff oddTilt)
open private cutA cutB c e bias from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private crossCoeff directedCoeff from D5.S3.Quantum.Semigroups.WuCubicAngularCertificate

private theorem quadratic_ge {P C : ℝ} (a : ℝ) (hP : 0 < P) :
    -(C ^ 2 / (4 * P)) ≤ P * a ^ 2 + C * a := by
  rw [← neg_div, div_le_iff₀ (by positivity : 0 < 4 * P)]
  nlinarith only [sq_nonneg (2 * P * a + C)]

/-- The matched angular estimate gives a positive normalized deficit at the literal spectrum
for every unitary frame. -/
theorem literal_normalizedDeficit (U : unitary Mat) :
    (3 / 1000 : ℝ) ≤ normalizedDeficit (6 / 5) U (2 / 3) (4 / 5) (9 / 10) := by
  let r : ℝ := 6 / 5
  let m : ℝ := 2 / 3
  let n : ℝ := 4 / 5
  let q : ℝ := 9 / 10
  let A := cutEnergy r m n q
  let B := cutBias r m n q
  let Z₀ := lowerCoeff r m n q
  let Z₂ := upperCoeff r n q
  let Zlong := longCoeff r m n q
  let L := matchedMixture A B
  let P₀ := (A 0 + Z₀ - L) / 2
  let P₂ := (A 2 + Z₂ - L) / 2
  let C₀ := B 0 / 2 - 2 * P₀
  let C₂ := B 2 / 2 - 2 * P₂
  have hcuts : 0 ≤ L ∧ L ≤ Z₀ ∧ L ≤ Z₂ ∧ L ≤ Zlong ∧ 0 < P₀ ∧ 0 < P₂ ∧
      3 / 1000 ≤ -(19147 / 1000000) + occupationCost A B Z₀ Z₂ -
        C₀ ^ 2 / (4 * P₀) - C₂ ^ 2 / (4 * P₂) := by
    norm_num [L, P₀, P₂, C₀, C₂, Z₀, Z₂, Zlong, A, B, r, m, n, q, matchedMixture,
      occupationCost, cutEnergy, cutBias, lowerCoeff, upperCoeff, longCoeff, cutA, cutB,
      crossCoeff, directedCoeff, c, e, bias, gamma]
  obtain ⟨hL, hleft, hright, hZlong, hP₀, hP₂, hmargin⟩ := hcuts
  have hthermal : -(19147 / 1000000 : ℝ) ≤ thermalCenter r m n q := literal_thermalCenter
  have hbound := matched_deficit_bound U (show 1 ≤ r by norm_num [r])
    (show 0 ≤ m by norm_num [m]) (show m ≤ n by norm_num [m, n])
    (show n ≤ q by norm_num [n, q]) (show q ≤ 1 by norm_num [q]) hL hleft hright
  change thermalCenter r m n q + occupationCost A B Z₀ Z₂ +
      (P₀ * oddTilt U 0 ^ 2 + P₂ * oddTilt U 3 ^ 2 +
        C₀ * oddTilt U 0 + C₂ * oddTilt U 3) +
      (Zlong / 4 * longFactor (tiltSum U) - L / 4) * tiltDiff U ^ 2 ≤
        normalizedDeficit r U m n q at hbound
  have hlong : 0 ≤ (Zlong / 4 * longFactor (tiltSum U) - L / 4) * tiltDiff U ^ 2 := by
    by_cases hs : tiltSum U = 0
    · have htilt (i : Fin 4) : 0 ≤ oddTilt U i := by
        unfold oddTilt oddProbability
        exact mul_nonneg (by norm_num)
          (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
      unfold tiltSum at hs
      have hd : tiltDiff U = 0 := by
        unfold tiltDiff
        linarith only [hs, htilt 0, htilt 3]
      simp [hd]
    · have hf : 1 ≤ longFactor (tiltSum U) := by
        rw [longFactor, ite_eq_right hs]
        exact le_max_left _ _
      have hz := hL.trans hZlong
      have hmul := mul_le_mul_of_nonneg_left hf (show 0 ≤ Zlong / 4 by positivity)
      exact mul_nonneg (by linarith only [hZlong, hmul]) (sq_nonneg _)
  have h₀ := quadratic_ge (C := C₀) (oddTilt U 0) hP₀
  have h₂ := quadratic_ge (C := C₂) (oddTilt U 3) hP₂
  change 3 / 1000 ≤ normalizedDeficit r U m n q
  linarith only [hthermal, hbound, hlong, h₀, h₂, hmargin]

end D5.S3.Quantum.Semigroups.WuCubicBoundaryCorner
