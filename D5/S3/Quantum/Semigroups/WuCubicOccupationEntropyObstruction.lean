/- GID: D5/S3/Quantum/Semigroups/WuCubicOccupationEntropyObstruction
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicOccupationEntropyObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict finite-amplitude entropy gap for matched-occupation complex CAR product states. -/

import OmegaBuild.Commands
import D5.S3.Quantum.Matrix.Tensor.KroneckerSqrt
import D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The fixed-occupation entropy obstruction at exponent three

At matched positive Gibbs temperature, local coherence in a faithful product state
makes the cubic-weighted entropy strictly larger than `4 * qStar`, the expression
derived from the quadratic defects. This tests the proposed entropy closure associated with
Wu, arXiv:2610.33686v1, (3.54). The cubic coefficient is the specialization of
Wu's one-qubit coefficient (3.4).
-/

compile_only_with_mathlib

noncomputable section

namespace D5.S3.Quantum.Semigroups.WuCubicOccupationEntropyObstruction

open Set

private def logGap (v : ℝ) : ℝ := Real.log (1 + v) - Real.log (1 - v)

private theorem hasDerivAt_logGap {v : ℝ} (hv : v ∈ Ico (0 : ℝ) 1) :
    HasDerivAt logGap (2 / (1 - v ^ 2)) v := by
  have hp : 0 < 1 + v := by linarith [hv.1]
  have hm : 0 < 1 - v := sub_pos.mpr hv.2
  have hplus := (hasDerivAt_id v).const_add (1 : ℝ)
  have hminus := (hasDerivAt_id v).const_sub (1 : ℝ)
  convert (hplus.log hp.ne').sub (hminus.log hm.ne') using 1
  · rfl
  simp only [id_eq]
  rw [show 1 - v ^ 2 = (1 + v) * (1 - v) by ring]
  field_simp [hp.ne', hm.ne']
  ring

private theorem logGap_convex : ConvexOn ℝ (Ico (0 : ℝ) 1) logGap := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ico _ _)
  · intro v hv
    exact (hasDerivAt_logGap hv).continuousAt.continuousWithinAt
  · intro v hv
    exact (hasDerivAt_logGap (interior_subset hv)).differentiableAt.differentiableWithinAt
  · intro u hu v hv huv
    have hu' : u ∈ Ico (0 : ℝ) 1 := interior_subset hu
    have hv' : v ∈ Ico (0 : ℝ) 1 := interior_subset hv
    rw [(hasDerivAt_logGap hu').deriv, (hasDerivAt_logGap hv').deriv]
    have hu₁ : 0 < 1 - u ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hu'.2) (show 0 < 1 + u by linarith [hu'.1])]
    have hv₁ : 0 < 1 - v ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hv'.2) (show 0 < 1 + v by linarith [hv'.1])]
    apply (div_le_div_iff₀ hu₁ hv₁).2
    nlinarith [mul_nonneg (sub_nonneg.mpr huv) (add_nonneg hu'.1 hv'.1)]

private theorem logGap_div_mono :
    MonotoneOn (fun v : ℝ => logGap v / v) (Ioo 0 1) := by
  intro u hu v hv huv
  have hsec := logGap_convex.secant_mono
    (show (0 : ℝ) ∈ Ico 0 1 from ⟨le_rfl, zero_lt_one⟩)
    (show u ∈ Ico 0 1 from ⟨hu.1.le, hu.2⟩)
    (show v ∈ Ico 0 1 from ⟨hv.1.le, hv.2⟩) hu.1.ne' hv.1.ne' huv
  simpa [show logGap 0 = 0 by simp [logGap]] using hsec

private def gap (a b z : ℝ) : ℝ := Real.sqrt ((b - a) ^ 2 + 4 * z)
private def upper (v : ℝ) : ℝ := (1 + v) / 2
private def lower (v : ℝ) : ℝ := (1 - v) / 2
private def xlogx (x : ℝ) : ℝ := x * Real.log x

private def entropyAt (a b z : ℝ) : ℝ :=
  xlogx (upper (gap a b z)) + xlogx (lower (gap a b z))

/-- The entropy increase of the two eigenvalues relative to the fixed diagonal. -/
def fixedOccupationEntropy (a b z : ℝ) : ℝ :=
  entropyAt a b z - xlogx a - xlogx b

/-- The zero-amplitude entropy slope. -/
def entropySlope (a b : ℝ) : ℝ := (Real.log b - Real.log a) / (b - a)

private theorem gap_mem {a b z : ℝ} (hab : a < b) (htrace : a + b = 1)
    (hz : 0 ≤ z) (hzab : z < a * b) : gap a b z ∈ Ioo 0 1 := by
  have hrad : 0 < (b - a) ^ 2 + 4 * z :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos (sub_pos.mpr hab)) (by positivity)
  have hidentity : (b - a) ^ 2 + 4 * (a * b) = 1 := by
    calc
      (b - a) ^ 2 + 4 * (a * b) = (a + b) ^ 2 := by ring
      _ = 1 := by rw [htrace]; norm_num
  refine ⟨Real.sqrt_pos.2 hrad, ?_⟩
  have hs := Real.sqrt_lt_sqrt hrad.le (show (b - a) ^ 2 + 4 * z < 1 by linarith)
  simpa [gap] using hs

private theorem gap_zero {a b : ℝ} (hab : a < b) : gap a b 0 = b - a := by
  simp [gap, Real.sqrt_sq_eq_abs, abs_of_pos (sub_pos.mpr hab)]

private theorem logGap_eq {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    logGap v = Real.log (upper v) - Real.log (lower v) := by
  unfold logGap upper lower
  rw [Real.log_div (by linarith [hv.1] : (1 + v) ≠ 0) (by norm_num),
    Real.log_div (sub_pos.mpr hv.2).ne' (by norm_num)]
  ring

private theorem hasDerivAt_entropyAt {a b z : ℝ} (hv : gap a b z ∈ Ioo 0 1) :
    HasDerivAt (entropyAt a b) (logGap (gap a b z) / gap a b z) z := by
  have hrad : (b - a) ^ 2 + 4 * z ≠ 0 := by
    intro h
    have hv' := hv.1
    simp [gap, h] at hv'
  have harg : HasDerivAt (fun y : ℝ => (b - a) ^ 2 + 4 * y) 4 z := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id z).const_mul (4 : ℝ)).const_add ((b - a) ^ 2))
  have hg : HasDerivAt (gap a b) (4 / (2 * gap a b z)) z := harg.sqrt hrad
  have hp : 0 < upper (gap a b z) := by unfold upper; linarith [hv.1]
  have hm : 0 < lower (gap a b z) := by unfold lower; linarith [hv.2]
  have hp' := (Real.hasDerivAt_mul_log hp.ne').comp z
    ((hg.const_add (1 : ℝ)).div_const (2 : ℝ))
  have hm' := (Real.hasDerivAt_mul_log hm.ne').comp z
    ((hg.const_sub (1 : ℝ)).div_const (2 : ℝ))
  convert hp'.add hm' using 1
  · rfl
  rw [logGap_eq hv]
  change (Real.log (upper (gap a b z)) - Real.log (lower (gap a b z))) / gap a b z =
    (Real.log (upper (gap a b z)) + 1) * (4 / (2 * gap a b z) / 2) +
      (Real.log (lower (gap a b z)) + 1) * (-(4 / (2 * gap a b z)) / 2)
  field_simp [hv.1.ne']
  ring

/-- The fixed diagonal entropy slope is a lower bound throughout the faithful interval. -/
theorem entropySlope_mul_le_fixedOccupationEntropy {a b z : ℝ}
    (hab : a < b) (htrace : a + b = 1) (hz : 0 ≤ z) (hzab : z < a * b) :
    entropySlope a b * z ≤ fixedOccupationEntropy a b z := by
  have hderiv (y : ℝ) (hy : y ∈ Icc 0 z) :=
    hasDerivAt_entropyAt (gap_mem hab htrace hy.1 (hy.2.trans_lt hzab))
  have hm := gap_mem hab htrace (le_refl (0 : ℝ)) (hz.trans_lt hzab)
  have hupper : upper (gap a b 0) = b := by rw [gap_zero hab]; unfold upper; linarith
  have hlower : lower (gap a b 0) = a := by rw [gap_zero hab]; unfold lower; linarith
  have hslope : logGap (gap a b 0) / gap a b 0 = entropySlope a b := by
    rw [logGap_eq hm, hupper, hlower, gap_zero hab, entropySlope]
  have hbound := (convex_Icc (0 : ℝ) z).mul_sub_le_image_sub_of_le_deriv
    (fun y hy => (hderiv y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hderiv y (interior_subset hy)).differentiableAt.differentiableWithinAt)
    (C := entropySlope a b) (by
      intro y hy
      have hy' : y ∈ Icc 0 z := interior_subset hy
      rw [(hderiv y hy').deriv, ← hslope]
      apply logGap_div_mono hm (gap_mem hab htrace hy'.1 (hy'.2.trans_lt hzab))
      unfold gap
      apply Real.sqrt_le_sqrt
      change (b - a) ^ 2 + 4 * 0 ≤ (b - a) ^ 2 + 4 * y
      linarith [hy'.1])
    0 ⟨le_rfl, hz⟩ z ⟨hz, le_rfl⟩ hz
  rw [sub_zero, show entropyAt a b 0 = xlogx b + xlogx a by
    simp only [entropyAt, hupper, hlower]] at hbound
  unfold fixedOccupationEntropy
  linarith

/-- The single nonzero matched-occupation quadratic defect, multiplied by `s`. -/
def occupationDefect (a b z : ℝ) : ℝ :=
  let s := Real.sqrt (a * b)
  let r := Real.sqrt (a * b - z)
  s * (s - r - z / (1 + 2 * r))

private theorem defect_upper {s r z η : ℝ} (hr : 0 < r) (hrs : r ≤ s)
    (hrsq : r ^ 2 = s ^ 2 - z) (hz : 0 ≤ z) (hη : 0 < η)
    (hamp : z ≤ s ^ 2 * η / (2 + η)) :
    4 * (s * (s - r - z / (1 + 2 * r))) ≤
      (2 / (1 + 2 * s)) * (1 + η / 2) * z := by
  have hs := hr.trans_le hrs
  have hsum : 0 < s + r := by positivity
  have hr₁ : 0 < 1 + 2 * r := by positivity
  have hs₁ : 0 < 1 + 2 * s := by positivity
  have hr₂ : 0 < r ^ 2 := by positivity
  have hfactor : (s - r) * (s + r) = z := by nlinarith only [hrsq]
  have hR :
      s - r - z / (1 + 2 * r) = z * ((1 + r - s) / ((s + r) * (1 + 2 * r))) := by
    rw [show s - r = z / (s + r) from (eq_div_iff hsum.ne').2 hfactor]
    field_simp [hsum.ne', hr₁.ne']
    ring
  have hfirst :
      (1 + r - s) / ((s + r) * (1 + 2 * r)) ≤ 1 / (2 * r * (1 + 2 * r)) := by
    have hd₁ : 0 < (s + r) * (1 + 2 * r) := mul_pos hsum hr₁
    have hd₂ : 0 < 2 * r * (1 + 2 * r) := by positivity
    apply (div_le_div_iff₀ hd₁ hd₂).2
    have hle : (1 + r - s) * (2 * r) ≤ s + r := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hrs) hr.le]
    simpa only [one_mul, ← mul_assoc] using mul_le_mul_of_nonneg_right hle hr₁.le
  have hsecond :
      2 * s / (r * (1 + 2 * r)) ≤ (2 / (1 + 2 * s)) * (s ^ 2 / r ^ 2) := by
    rw [div_mul_div_comm]
    have hd₁ : 0 < r * (1 + 2 * r) := mul_pos hr hr₁
    have hd₂ : 0 < (1 + 2 * s) * r ^ 2 := mul_pos hs₁ hr₂
    apply (div_le_div_iff₀ hd₁ hd₂).2
    have hle := mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * s) hr.le)
      (sub_nonneg.mpr hrs)
    nlinarith only [hle]
  have hthird : s ^ 2 / r ^ 2 ≤ 1 + η / 2 := by
    have hz' := (le_div_iff₀ (by positivity : 0 < 2 + η)).1 hamp
    apply (div_le_iff₀ hr₂).2
    rw [hrsq]
    nlinarith only [hz']
  rw [hR]
  calc
    4 * (s * (z * ((1 + r - s) / ((s + r) * (1 + 2 * r))))) ≤
        (4 * s * z) * (1 / (2 * r * (1 + 2 * r))) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hfirst (show 0 ≤ 4 * s * z by positivity)
    _ = (2 * s / (r * (1 + 2 * r))) * z := by
      field_simp [hr.ne', hr₁.ne']
      ring
    _ ≤ (2 / (1 + 2 * s)) * (s ^ 2 / r ^ 2) * z :=
      mul_le_mul_of_nonneg_right hsecond hz
    _ ≤ (2 / (1 + 2 * s)) * (1 + η / 2) * z :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hthird (by positivity)) hz

/-- A uniform strict gap at every positive amplitude in the stated interval. -/
theorem finite_amplitude_obstruction {a b z α η : ℝ}
    (ha : 0 < a) (hab : a < b) (htrace : a + b = 1)
    (hη : 0 < η) (hz : 0 < z)
    (hamp : z ≤ a * b * η / (2 + η))
    (hα : α * entropySlope a b = 2 * (1 + η) / (1 + 2 * Real.sqrt (a * b))) :
    0 < η * z / (1 + 2 * Real.sqrt (a * b)) ∧
      η * z / (1 + 2 * Real.sqrt (a * b)) ≤
        α * fixedOccupationEntropy a b z - 4 * occupationDefect a b z := by
  have hb := ha.trans hab
  have hab₀ := mul_pos ha hb
  have hηden : 0 < 2 + η := by positivity
  have hzab : z < a * b := hamp.trans_lt <|
    (div_lt_iff₀ hηden).2 (by nlinarith only [hab₀])
  let s := Real.sqrt (a * b)
  let r := Real.sqrt (a * b - z)
  have hs : 0 < s := Real.sqrt_pos.2 hab₀
  have hr : 0 < r := Real.sqrt_pos.2 (sub_pos.mpr hzab)
  have hrs : r ≤ s := Real.sqrt_le_sqrt (by linarith)
  have hss : s ^ 2 = a * b := Real.sq_sqrt hab₀.le
  have hrr : r ^ 2 = s ^ 2 - z := by rw [hss]; exact Real.sq_sqrt (sub_nonneg.mpr hzab.le)
  have hψ : 0 < entropySlope a b :=
    div_pos (sub_pos.mpr (Real.log_lt_log ha hab)) (sub_pos.mpr hab)
  have hαpos : 0 < α := by
    have hp : 0 < α * entropySlope a b := by rw [hα]; positivity
    by_contra! hn
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hn hψ.le)) hp
  have hE := mul_le_mul_of_nonneg_left
    (entropySlope_mul_le_fixedOccupationEntropy hab htrace hz.le hzab) hαpos.le
  rw [← mul_assoc, hα] at hE
  have hQ := defect_upper hr hrs hrr hz.le hη (by rwa [hss])
  change 0 < η * z / (1 + 2 * s) ∧
    η * z / (1 + 2 * s) ≤ α * fixedOccupationEntropy a b z - 4 * (s * (s - r - z / (1 + 2 * r)))
  refine ⟨div_pos (mul_pos hη hz) (by positivity), ?_⟩
  have hdiff :
      (2 * (1 + η) / (1 + 2 * s)) * z -
        (2 / (1 + 2 * s)) * (1 + η / 2) * z = η * z / (1 + 2 * s) := by
    field_simp [show 1 + 2 * s ≠ 0 by positivity]
    ring
  rw [← hdiff]
  exact sub_le_sub hE hQ

/-- The lower Gibbs occupation at half-gap `h`. -/
def gibbsLow (h : ℝ) : ℝ := Real.exp (-h) / (2 * Real.cosh h)

/-- The upper Gibbs occupation at half-gap `h`. -/
def gibbsHigh (h : ℝ) : ℝ := Real.exp h / (2 * Real.cosh h)

/-- Wu's expression (3.55) at `β = 2*h`, `s = 3`, and `s' = 3/2`. -/
def cubicCoefficient (h : ℝ) : ℝ :=
  (9 / 2) * Real.sinh (h / 3) * Real.sinh (2 * h / 3) / (2 * h * Real.sinh h)

/-- Relative excess of the cubic coefficient over the quadratic coefficient. -/
def cubicExcess (h : ℝ) : ℝ :=
  let c := Real.cosh (h / 3)
  (c - 1) * (c + 2) / (2 * (2 * c + 1) ^ 2)

private theorem gibbs_properties {h : ℝ} (hh : 0 < h) :
    0 < gibbsLow h ∧ gibbsLow h < gibbsHigh h ∧ gibbsLow h + gibbsHigh h = 1 := by
  have hd : 0 < 2 * Real.cosh h := by positivity
  refine ⟨div_pos (Real.exp_pos _) hd,
    (div_lt_div_iff_of_pos_right hd).2 (Real.exp_lt_exp.mpr (by linarith)), ?_⟩
  rw [gibbsLow, gibbsHigh, ← add_div, Real.cosh_eq,
    show 2 * ((Real.exp h + Real.exp (-h)) / 2) = Real.exp h + Real.exp (-h) by ring,
    add_comm (Real.exp (-h)) (Real.exp h),
    div_self (show Real.exp h + Real.exp (-h) ≠ 0 by positivity)]

private theorem cubicExcess_pos {h : ℝ} (hh : 0 < h) : 0 < cubicExcess h := by
  have hc : 1 < Real.cosh (h / 3) := Real.one_lt_cosh.mpr (by positivity)
  unfold cubicExcess
  exact div_pos (mul_pos (sub_pos.mpr hc) (by positivity)) (by positivity)

private theorem cubicCoefficient_mul_entropySlope {h : ℝ} (hh : 0 < h) :
    cubicCoefficient h * entropySlope (gibbsLow h) (gibbsHigh h) =
      2 * (1 + cubicExcess h) / (1 + 2 * Real.sqrt (gibbsLow h * gibbsHigh h)) := by
  let C := Real.cosh h
  let S := Real.sinh h
  let c := Real.cosh (h / 3)
  have hC : 1 < C := Real.one_lt_cosh.mpr hh.ne'
  have hS : 0 < S := Real.sinh_pos_iff.mpr hh
  have hc : 1 < c := Real.one_lt_cosh.mpr (by positivity)
  have hC₀ : 0 < C := Real.cosh_pos h
  have hc₁ : 0 < 2 * c + 1 := by linarith
  have hC₁ : 0 < C + 1 := by linarith
  have hd : 0 < 2 * C := by positivity
  have hdlog : Real.log (gibbsHigh h) - Real.log (gibbsLow h) = 2 * h := by
    change Real.log (Real.exp h / (2 * C)) - Real.log (Real.exp (-h) / (2 * C)) = _
    rw [Real.log_div (Real.exp_pos h).ne' hd.ne',
      Real.log_div (Real.exp_pos (-h)).ne' hd.ne', Real.log_exp, Real.log_exp]
    ring
  have hm : gibbsHigh h - gibbsLow h = S / C := by
    change Real.exp h / (2 * C) - Real.exp (-h) / (2 * C) = S / C
    rw [← sub_div, show S = (Real.exp h - Real.exp (-h)) / 2 from Real.sinh_eq h]
    field_simp [hC₀.ne']
  have hs : Real.sqrt (gibbsLow h * gibbsHigh h) = 1 / (2 * C) := by
    change Real.sqrt ((Real.exp (-h) / (2 * C)) * (Real.exp h / (2 * C))) = _
    rw [div_mul_div_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [← show (1 / (2 * C)) ^ 2 = 1 / ((2 * C) * (2 * C)) by rw [div_pow, one_pow, pow_two]]
    exact Real.sqrt_sq (by positivity)
  have hsub : C - c = 2 * (Real.sinh (h / 3) * Real.sinh (2 * h / 3)) := by
    have hadd := Real.cosh_add (x := 2 * h / 3) (y := h / 3)
    have hminus := Real.cosh_sub (x := 2 * h / 3) (y := h / 3)
    rw [show 2 * h / 3 + h / 3 = h by ring] at hadd
    rw [show 2 * h / 3 - h / 3 = h / 3 by ring] at hminus
    change Real.cosh h - Real.cosh (h / 3) = _
    linear_combination hadd - hminus
  have hα : cubicCoefficient h = (9 / 8) * (C - c) / (h * S) := by
    unfold cubicCoefficient
    change _ / (2 * h * S) = _
    calc
      _ = (9 / 8) * (2 * (Real.sinh (h / 3) * Real.sinh (2 * h / 3))) / (h * S) := by
        ring
      _ = _ := by rw [← hsub]
  have htriple : C = 4 * c ^ 3 - 3 * c := by
    change Real.cosh h = 4 * Real.cosh (h / 3) ^ 3 - 3 * Real.cosh (h / 3)
    calc
      Real.cosh h = Real.cosh (2 * (h / 3) + h / 3) := congrArg Real.cosh (by ring)
      _ = _ := by
        rw [Real.cosh_add, Real.cosh_two_mul, Real.sinh_two_mul]
        linear_combination
          (-3 * Real.cosh (h / 3)) * Real.cosh_sq_sub_sinh_sq (h / 3)
  have hfactor₁ : C - 1 = (c - 1) * (2 * c + 1) ^ 2 := by rw [htriple]; ring
  have hfactor₂ : C - c = 4 * c * (c - 1) * (c + 1) := by rw [htriple]; ring
  have hSsq : S ^ 2 = (C + 1) * (C - 1) := by
    change Real.sinh h ^ 2 = (Real.cosh h + 1) * (Real.cosh h - 1)
    nlinarith only [Real.cosh_sq_sub_sinh_sq h]
  have hden : 0 < 1 + 2 * Real.sqrt (gibbsLow h * gibbsHigh h) := by positivity
  apply (eq_div_iff hden.ne').2
  rw [hα, entropySlope, hm, hdlog, hs]
  change (9 / 8) * (C - c) / (h * S) * (2 * h / (S / C)) * (1 + 2 * (1 / (2 * C))) =
    2 * (1 + (c - 1) * (c + 2) / (2 * (2 * c + 1) ^ 2))
  calc
    _ = (9 / 4) * ((C - c) * (C + 1)) / S ^ 2 := by
      field_simp [hh.ne', hS.ne', hC₀.ne']
      ring
    _ = (9 / 4) * (C - c) / (C - 1) := by
      rw [hSsq]
      field_simp [hC₁.ne', (sub_pos.mpr hC).ne']
    _ = 2 * (1 + (c - 1) * (c + 2) / (2 * (2 * c + 1) ^ 2)) := by
      rw [hfactor₁, hfactor₂]
      field_simp [(sub_pos.mpr hc).ne', hc₁.ne']
      ring

section Physical

open _root_.Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open TwistedTwoModeOUComparison (modeJump)
open D5.S3.Quantum.Matrix.Tensor.KroneckerSqrt (sqrt_kronecker)

abbrev Qubit := Matrix (Fin 2) (Fin 2) ℂ
abbrev TwoMode := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

private def occupations (a b : ℝ) : Fin 2 → ℝ := ![a, b]

/-- The local Gibbs matrix in increasing occupation order. -/
def localGibbs (a b : ℝ) : Qubit :=
  diagonal (fun i => (occupations a b i : ℂ))

/-- The coherent local density, with unconstrained complex phase. -/
def coherentDensity (a b : ℝ) (w : ℂ) : Qubit := !![(a : ℂ), w; star w, (b : ℂ)]

/-- The product-state witness in the occupation basis of the literal CAR jumps. -/
def witness (a b : ℝ) (w : ℂ) : TwoMode := localGibbs a b ⊗ₖ coherentDensity a b w

/-- Ordinary-trace Umegaki relative entropy for the faithful states used here. -/
def traceRelativeEntropy {n : Type*} [Fintype n] [DecidableEq n]
    (ρ D : Matrix n n ℂ) : ℝ := (ρ * (CFC.log ρ - CFC.log D)).trace.re

/-- Hole and particle probabilities, respectively, measured with a literal lowering jump. -/
def hole (ρ : TwoMode) (k : Fin 2) : ℝ :=
  (ρ * (modeJump k * (modeJump k)ᴴ)).trace.re

def particle (ρ : TwoMode) (k : Fin 2) : ℝ :=
  (ρ * ((modeJump k)ᴴ * modeJump k)).trace.re

/-- The quadratic overlap computed using the positive square root of the state. -/
def halfOverlap (ρ : TwoMode) (k : Fin 2) : ℝ :=
  (CFC.sqrt ρ * modeJump k * CFC.sqrt ρ * (modeJump k)ᴴ).trace.re

/-- Matched-occupation quadratic defect, summed over the original CAR modes. -/
def qStar (ρ : TwoMode) : ℝ :=
  ∑ k : Fin 2, Real.sqrt (hole ρ k * particle ρ k) *
    (Real.sqrt (hole ρ k * particle ρ k) - halfOverlap ρ k)

private theorem localGibbs_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (localGibbs a b).PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  have hi : 0 < occupations a b i := by fin_cases i <;> assumption
  exact_mod_cast hi

private theorem coherent_hermitian (a b : ℝ) (w : ℂ) :
    (coherentDensity a b w).IsHermitian := by
  change (coherentDensity a b w)ᴴ = coherentDensity a b w
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coherentDensity, Matrix.conjTranspose_apply]

private theorem localGibbs_trace {a b : ℝ} (ht : a + b = 1) : (localGibbs a b).trace = 1 := by
  simp [localGibbs, occupations, Matrix.trace_diagonal, Fin.sum_univ_two,
    ← Complex.ofReal_add, ht]

private theorem coherent_trace {a b : ℝ} (ht : a + b = 1) (w : ℂ) :
    (coherentDensity a b w).trace = 1 := by
  simp [coherentDensity, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two,
    ← Complex.ofReal_add, ht]

private theorem coherent_eigen_arithmetic {a b : ℝ} (ht : a + b = 1) (w : ℂ) :
    let e := (coherent_hermitian a b w).eigenvalues
    e 0 + e 1 = 1 ∧ e 0 * e 1 = a * b - Complex.normSq w := by
  dsimp only
  have hH := coherent_hermitian a b w
  have hsum := hH.trace_eq_sum_eigenvalues
  have hprod := hH.det_eq_prod_eigenvalues
  have hdet : (coherentDensity a b w).det = ((a * b - Complex.normSq w : ℝ) : ℂ) := by
    rw [Matrix.det_fin_two]
    change (a : ℂ) * (b : ℂ) - w * star w = _
    simp only [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  rw [coherent_trace ht, Fin.sum_univ_two] at hsum
  rw [hdet, Fin.prod_univ_two] at hprod
  constructor
  · simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.add_re, Complex.ofReal_re,
      Complex.one_re] using congrArg Complex.re hsum.symm
  · simpa only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_mul,
      Complex.ofReal_re] using congrArg Complex.re hprod.symm

private theorem coherent_pos {a b : ℝ} {w : ℂ} (ht : a + b = 1)
    (hz : Complex.normSq w < a * b) : (coherentDensity a b w).PosDef := by
  have hH := coherent_hermitian a b w
  let e := hH.eigenvalues
  obtain ⟨hsum, hprod⟩ : e 0 + e 1 = 1 ∧ e 0 * e 1 = a * b - Complex.normSq w :=
    coherent_eigen_arithmetic ht w
  have hp : 0 < e 0 * e 1 := by rw [hprod]; exact sub_pos.mpr hz
  refine hH.posDef_iff_eigenvalues_pos.mpr ?_
  intro i
  change 0 < e i
  fin_cases i
  · change 0 < e 0
    by_contra! h0
    exact hp.not_ge (mul_nonpos_of_nonpos_of_nonneg h0 (by linarith only [hsum, h0]))
  · change 0 < e 1
    by_contra! h1
    exact hp.not_ge (mul_nonpos_of_nonneg_of_nonpos (by linarith only [hsum, h1]) h1)

private theorem trace_cfc_entropy {A : Qubit} (hA : A.IsHermitian) :
    (A * CFC.log A).trace.re = ∑ i, xlogx (hA.eigenvalues i) := by
  let U : Qubit := hA.eigenvectorUnitary
  let D : Qubit := diagonal (fun i => (hA.eigenvalues i : ℂ))
  let L : Qubit := diagonal (fun i => (Real.log (hA.eigenvalues i) : ℂ))
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  have hspec : A = U * D * Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, U, D, RCLike.ofReal_eq_complex_ofReal,
      Function.comp_def, Matrix.star_eq_conjTranspose] using hA.spectral_theorem
  have hlog : CFC.log A = U * L * Uᴴ := by
    rw [CFC.log, hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    rfl
  have hmul : U * D * Uᴴ * (U * L * Uᴴ) = U * (D * L) * Uᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
  have hproduct : A * CFC.log A = U * (D * L) * Uᴴ := by rw [hlog, hspec, hmul]
  rw [hproduct, Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  simp only [D, L, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum,
    ← Complex.ofReal_mul, Complex.ofReal_re, xlogx]

private theorem coherent_entropy_moment {a b : ℝ} (ht : a + b = 1) (w : ℂ) :
    (coherentDensity a b w * CFC.log (coherentDensity a b w)).trace.re =
      entropyAt a b (Complex.normSq w) := by
  let e := (coherent_hermitian a b w).eigenvalues
  let z := Complex.normSq w
  let v := gap a b z
  obtain ⟨hsum, hprod⟩ : e 0 + e 1 = 1 ∧ e 0 * e 1 = a * b - z :=
    coherent_eigen_arithmetic ht w
  have hz : 0 ≤ z := Complex.normSq_nonneg w
  have hv : v ^ 2 = (b - a) ^ 2 + 4 * z := Real.sq_sqrt (by positivity)
  have hab : (b - a) ^ 2 + 4 * (a * b) = 1 := by
    calc
      _ = (a + b) ^ 2 := by ring
      _ = 1 := by rw [ht]; norm_num
  have he : (e 0 - upper v) * (e 0 - lower v) = 0 := by
    unfold upper lower
    linear_combination e 0 * hsum - hprod - hv / 4 - hab / 4
  have hbands : upper v + lower v = 1 := by unfold upper lower; ring
  rw [trace_cfc_entropy (coherent_hermitian a b w), Fin.sum_univ_two]
  change xlogx (e 0) + xlogx (e 1) = xlogx (upper v) + xlogx (lower v)
  rcases (mul_eq_zero.mp he).imp sub_eq_zero.mp sub_eq_zero.mp with h0 | h0
  · have h1 : e 1 = lower v := by linarith only [hsum, hbands, h0]
    rw [h0, h1]
  · have h1 : e 1 = upper v := by linarith only [hsum, hbands, h0]
    rw [h0, h1]
    exact add_comm _ _

private theorem coherent_trace_log_reference (a b : ℝ) (w : ℂ) :
    (coherentDensity a b w * CFC.log (localGibbs a b)).trace.re = xlogx a + xlogx b := by
  have hlog : CFC.log (localGibbs a b) =
      diagonal (fun i => (Real.log (occupations a b i) : ℂ)) := by
    simpa only [CFC.log, localGibbs, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      Matrix.cfc_diagonal_real (𝕜 := ℂ) (occupations a b) Real.log
  rw [hlog]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Fin.sum_univ_two,
    coherentDensity, Matrix.of_apply, occupations, Matrix.cons_val_zero, Matrix.cons_val_one,
    ← Complex.ofReal_mul, Complex.add_re, Complex.ofReal_re, xlogx]

private theorem coherent_relativeEntropy {a b : ℝ} (ht : a + b = 1) (w : ℂ) :
    traceRelativeEntropy (coherentDensity a b w) (localGibbs a b) =
      fixedOccupationEntropy a b (Complex.normSq w) := by
  rw [traceRelativeEntropy, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
    coherent_entropy_moment ht w, coherent_trace_log_reference]
  unfold fixedOccupationEntropy
  ring

private theorem log_tensor {A B : Qubit} (hA : A.PosDef) (hB : B.PosDef) :
    CFC.log (A ⊗ₖ B) =
      CFC.log A ⊗ₖ (1 : Qubit) + (1 : Qubit) ⊗ₖ CFC.log B := by
  let U := hA.isHermitian.eigenvectorUnitary
  let V := hB.isHermitian.eigenvectorUnitary
  let a := hA.isHermitian.eigenvalues
  let b := hB.isHermitian.eigenvalues
  let W : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
    ⟨(U : Qubit) ⊗ₖ (V : Qubit), Matrix.kronecker_mem_unitary U.2 V.2⟩
  have hU : (U : Qubit) * (U : Qubit)ᴴ = 1 := Unitary.coe_mul_star_self U
  have hV : (V : Qubit) * (V : Qubit)ᴴ = 1 := Unitary.coe_mul_star_self V
  have ha : ∀ i, 0 < a i := hA.eigenvalues_pos
  have hb : ∀ i, 0 < b i := hB.eigenvalues_pos
  have hspecA : A = (U : Qubit) * diagonal (fun i => (a i : ℂ)) * (U : Qubit)ᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, U, a, RCLike.ofReal_eq_complex_ofReal,
      Function.comp_def, Matrix.star_eq_conjTranspose] using hA.isHermitian.spectral_theorem
  have hspecB : B = (V : Qubit) * diagonal (fun i => (b i : ℂ)) * (V : Qubit)ᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, V, b, RCLike.ofReal_eq_complex_ofReal,
      Function.comp_def, Matrix.star_eq_conjTranspose] using hB.isHermitian.spectral_theorem
  have hspecAB : A ⊗ₖ B = (W : TwoMode) *
      diagonal (fun i => ((a i.1 * b i.2 : ℝ) : ℂ)) * (W : TwoMode)ᴴ := by
    calc
      _ = ((U : Qubit) * diagonal (fun i => (a i : ℂ)) * (U : Qubit)ᴴ) ⊗ₖ
          ((V : Qubit) * diagonal (fun i => (b i : ℂ)) * (V : Qubit)ᴴ) :=
        congrArg₂ (fun X Y : Qubit => X ⊗ₖ Y) hspecA hspecB
      _ = _ := by
        rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul,
          Matrix.diagonal_kronecker_diagonal]
        simp only [W, Matrix.conjTranspose_kronecker, Complex.ofReal_mul]
  have hlogA : CFC.log A = (U : Qubit) *
      diagonal (fun i => (Real.log (a i) : ℂ)) * (U : Qubit)ᴴ := by
    rw [CFC.log, hA.isHermitian.cfc_eq]
    exact hA.isHermitian.cfc_eq_any_unitary (U := U) (D := a) hspecA Real.log
  have hlogB : CFC.log B = (V : Qubit) *
      diagonal (fun i => (Real.log (b i) : ℂ)) * (V : Qubit)ᴴ := by
    rw [CFC.log, hB.isHermitian.cfc_eq]
    exact hB.isHermitian.cfc_eq_any_unitary (U := V) (D := b) hspecB Real.log
  have hAB := (hA.kronecker hB).isHermitian
  have hlogAB : CFC.log (A ⊗ₖ B) = (W : TwoMode) *
      diagonal (fun i => (Real.log (a i.1 * b i.2) : ℂ)) * (W : TwoMode)ᴴ := by
    rw [CFC.log, hAB.cfc_eq]
    exact hAB.cfc_eq_any_unitary (U := W) (D := fun i => a i.1 * b i.2) hspecAB Real.log
  have hdiag : diagonal (fun i : Fin 2 × Fin 2 => (Real.log (a i.1 * b i.2) : ℂ)) =
      diagonal (fun i => (Real.log (a i) : ℂ)) ⊗ₖ (1 : Qubit) +
        (1 : Qubit) ⊗ₖ diagonal (fun i => (Real.log (b i) : ℂ)) := by
    simp only [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal, mul_one, one_mul,
      Matrix.diagonal_add, Matrix.diagonal_eq_diagonal_iff]
    intro i
    rw [Real.log_mul (ha i.1).ne' (hb i.2).ne', Complex.ofReal_add]
  rw [hlogAB, hlogA, hlogB, hdiag, mul_add, add_mul]
  simp only [W, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, hU, hV]

private theorem witness_entropy {a b : ℝ} {w : ℂ} (ha : 0 < a) (hb : 0 < b)
    (ht : a + b = 1) (hw : Complex.normSq w < a * b) :
    traceRelativeEntropy (witness a b w) (localGibbs a b ⊗ₖ localGibbs a b) =
      fixedOccupationEntropy a b (Complex.normSq w) := by
  let d := localGibbs a b
  let σ := coherentDensity a b w
  have hd : d.PosDef := localGibbs_pos ha hb
  have hσ : σ.PosDef := coherent_pos ht hw
  have htr : d.trace = 1 := localGibbs_trace ht
  change ((d ⊗ₖ σ) * (CFC.log (d ⊗ₖ σ) - CFC.log (d ⊗ₖ d))).trace.re = _
  rw [log_tensor hd hσ, log_tensor hd hd, add_sub_add_left_eq_sub,
    Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  simp only [← Matrix.mul_kronecker_mul, mul_one, Matrix.trace_kronecker, htr, one_mul]
  simpa only [traceRelativeEntropy, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] using
    coherent_relativeEntropy ht w

private theorem coherent_sq {a b : ℝ} (ht : a + b = 1) (w : ℂ) :
    coherentDensity a b w * coherentDensity a b w =
      coherentDensity a b w - (a * b - Complex.normSq w) • (1 : Qubit) := by
  have htr : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast ht
  have hnorm : w * starRingEnd ℂ w = (Complex.normSq w : ℂ) := Complex.mul_conj w
  have hnorm' : starRingEnd ℂ w * w = (Complex.normSq w : ℂ) := by rw [mul_comm, hnorm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coherentDensity, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Complex.real_smul, hnorm, hnorm',
      Complex.ofReal_mul, Complex.ofReal_sub]
  · linear_combination (a : ℂ) * htr
  · linear_combination w * htr
  · linear_combination starRingEnd ℂ w * htr
  · linear_combination (b : ℂ) * htr

private theorem coherent_sqrt {a b : ℝ} {w : ℂ} (ht : a + b = 1)
    (hz : Complex.normSq w < a * b) :
    let r := Real.sqrt (a * b - Complex.normSq w)
    CFC.sqrt (coherentDensity a b w) =
      (Real.sqrt (1 + 2 * r))⁻¹ • (coherentDensity a b w + r • (1 : Qubit)) := by
  let σ := coherentDensity a b w
  let r := Real.sqrt (a * b - Complex.normSq w)
  let t := Real.sqrt (1 + 2 * r)
  have hσ : σ.PosDef := coherent_pos ht hz
  have hr : 0 < r := Real.sqrt_pos.2 (sub_pos.mpr hz)
  have hrr : r ^ 2 = a * b - Complex.normSq w := Real.sq_sqrt (sub_nonneg.mpr hz.le)
  have htpos : 0 < t := Real.sqrt_pos.2 (by positivity)
  have htt : t ^ 2 = 1 + 2 * r := Real.sq_sqrt (by positivity)
  have hsq : (σ + r • (1 : Qubit)) * (σ + r • (1 : Qubit)) = (1 + 2 * r) • σ := by
    calc
      _ = σ * σ + (2 * r) • σ + r ^ 2 • (1 : Qubit) := by
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul,
          smul_add, smul_smul, two_mul, add_smul, pow_two]
        abel
      _ = _ := by
        rw [show σ * σ = σ - (a * b - Complex.normSq w) • (1 : Qubit) from coherent_sq ht w,
          hrr, add_smul, one_smul]
        abel
  change CFC.sqrt σ = t⁻¹ • (σ + r • (1 : Qubit))
  apply CFC.sqrt_unique
  · rw [smul_mul_smul_comm, hsq, smul_smul]
    have hscale : t⁻¹ * t⁻¹ * (1 + 2 * r) = 1 := by
      field_simp [htpos.ne']
      nlinarith only [htt]
    rw [hscale, one_smul]
  · exact ((hσ.posSemidef.add (Matrix.PosSemidef.one.smul hr.le)).smul
      (inv_nonneg.mpr htpos.le)).nonneg

private theorem localGibbs_sqrt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    CFC.sqrt (localGibbs a b) = localGibbs (Real.sqrt a) (Real.sqrt b) := by
  rw [CFC.sqrt_eq_real_sqrt _ (localGibbs_pos ha hb).posSemidef.nonneg,
    cfcₙ_eq_cfc (hf0 := Real.sqrt_zero)]
  have hlog : cfc Real.sqrt (localGibbs a b) =
      diagonal (fun i => (Real.sqrt (occupations a b i) : ℂ)) := by
    simpa only [localGibbs, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      Matrix.cfc_diagonal_real (𝕜 := ℂ) (occupations a b) Real.sqrt
  rw [hlog]
  refine congrArg diagonal (funext fun i => ?_)
  fin_cases i <;> rfl

private def localLowering : Qubit := !![0, 1; 0, 0]
private def localParity : Qubit := diagonal ![-1, 1]

private theorem mode_zero : modeJump 0 = localLowering ⊗ₖ (1 : Qubit) := rfl
private theorem mode_one : modeJump 1 = localParity ⊗ₖ localLowering := rfl

private theorem trace_local_occupation (A : Qubit) :
    (A * (localLowering * localLoweringᴴ)).trace = A 0 0 ∧
    (A * (localLoweringᴴ * localLowering)).trace = A 1 1 := by
  constructor <;>
    simp only [localLowering, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, star_zero, star_one, mul_zero, mul_one, zero_mul, one_mul,
      add_zero, zero_add]

private theorem parity_products :
    localParity * localParityᴴ = 1 ∧ localParityᴴ * localParity = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [localParity, Matrix.diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Matrix.one_apply]

private theorem witness_occupations {a b : ℝ} (ht : a + b = 1) (w : ℂ) (k : Fin 2) :
    hole (witness a b w) k = a ∧ particle (witness a b w) k = b := by
  fin_cases k
  · change hole (witness a b w) 0 = a ∧ particle (witness a b w) 0 = b
    simp only [hole, particle, mode_zero, witness, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.trace_kronecker, coherent_trace ht w, mul_one,
      (trace_local_occupation (localGibbs a b)).1, (trace_local_occupation (localGibbs a b)).2]
    simp [localGibbs, occupations]
  · change hole (witness a b w) 1 = a ∧ particle (witness a b w) 1 = b
    simp only [hole, particle, mode_one, witness, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, parity_products.1, parity_products.2, Matrix.mul_one,
      Matrix.trace_kronecker, localGibbs_trace ht, one_mul,
      (trace_local_occupation (coherentDensity a b w)).1,
      (trace_local_occupation (coherentDensity a b w)).2]
    simp [coherentDensity]

private theorem trace_local_overlap (A : Qubit) :
    (A * localLowering * A * localLoweringᴴ).trace = A 0 0 * A 1 1 := by
  norm_num [localLowering, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.conjTranspose_apply]

private theorem trace_parity_overlap {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : a + b = 1) :
    (CFC.sqrt (localGibbs a b) * localParity * CFC.sqrt (localGibbs a b) *
      localParityᴴ).trace = 1 := by
  let S := CFC.sqrt (localGibbs a b)
  have hcomm : localParity * S = S * localParity := by
    change localParity * CFC.sqrt (localGibbs a b) = CFC.sqrt (localGibbs a b) * localParity
    rw [localGibbs_sqrt ha hb]
    unfold localGibbs localParity
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun _ => mul_comm _ _)
  change (S * localParity * S * localParityᴴ).trace = 1
  rw [Matrix.mul_assoc S localParity S, hcomm, ← Matrix.mul_assoc S S localParity,
    Matrix.mul_assoc (S * S), parity_products.1, Matrix.mul_one]
  change (CFC.sqrt (localGibbs a b) * CFC.sqrt (localGibbs a b)).trace = 1
  rw [CFC.sqrt_mul_sqrt_self _ (localGibbs_pos ha hb).posSemidef.nonneg,
    localGibbs_trace ht]

private theorem witness_qStar {a b : ℝ} {w : ℂ} (ha : 0 < a) (hb : 0 < b)
    (ht : a + b = 1) (hw : Complex.normSq w < a * b) :
    qStar (witness a b w) = occupationDefect a b (Complex.normSq w) := by
  let d := localGibbs a b
  let σ := coherentDensity a b w
  let r := Real.sqrt (a * b - Complex.normSq w)
  let t := Real.sqrt (1 + 2 * r)
  have hd : d.PosDef := localGibbs_pos ha hb
  have hσ : σ.PosDef := coherent_pos ht hw
  have hroot : CFC.sqrt (witness a b w) = CFC.sqrt d ⊗ₖ CFC.sqrt σ :=
    sqrt_kronecker d σ hd.posSemidef hσ.posSemidef
  have hoverlap₀ : halfOverlap (witness a b w) 0 = Real.sqrt (a * b) := by
    rw [halfOverlap, hroot, mode_zero, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one]
    simp only [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
      CFC.sqrt_mul_sqrt_self σ hσ.posSemidef.nonneg, show σ.trace = 1 from coherent_trace ht w,
      mul_one, trace_local_overlap, show CFC.sqrt d = _ from localGibbs_sqrt ha hb]
    simp [localGibbs, occupations, ← Complex.ofReal_mul, Real.sqrt_mul ha.le]
  have hr : 0 < r := Real.sqrt_pos.2 (sub_pos.mpr hw)
  have htpos : 0 < t := Real.sqrt_pos.2 (by positivity)
  have htt : t ^ 2 = 1 + 2 * r := Real.sq_sqrt (by positivity)
  have hrr : r ^ 2 = a * b - Complex.normSq w := Real.sq_sqrt (sub_nonneg.mpr hw.le)
  have hS : CFC.sqrt σ = t⁻¹ • (σ + r • (1 : Qubit)) := coherent_sqrt ht hw
  have h00 : (CFC.sqrt σ) 0 0 = (↑(t⁻¹ * (a + r)) : ℂ) := by
    rw [hS, Matrix.smul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq]
    change t⁻¹ • ((a : ℂ) + r • (1 : ℂ)) = _
    simp only [Complex.real_smul, mul_one, Complex.ofReal_mul, Complex.ofReal_add]
  have h11 : (CFC.sqrt σ) 1 1 = (↑(t⁻¹ * (b + r)) : ℂ) := by
    rw [hS, Matrix.smul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq]
    change t⁻¹ • ((b : ℂ) + r • (1 : ℂ)) = _
    simp only [Complex.real_smul, mul_one, Complex.ofReal_mul, Complex.ofReal_add]
  have hoverlap₁ : halfOverlap (witness a b w) 1 = r + Complex.normSq w / (1 + 2 * r) := by
    rw [halfOverlap, hroot, mode_one, Matrix.conjTranspose_kronecker]
    simp only [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
      show (CFC.sqrt d * localParity * CFC.sqrt d * localParityᴴ).trace = 1 from
        trace_parity_overlap ha hb ht, one_mul, trace_local_overlap, h00, h11,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    have hden : 0 < 1 + 2 * r := by positivity
    calc
      _ = ((a + r) * (b + r)) / t ^ 2 := by
        field_simp [htpos.ne']
      _ = (r * (1 + 2 * r) + Complex.normSq w) / (1 + 2 * r) := by
        rw [htt]
        congr 1
        linear_combination r * ht - hrr
      _ = _ := by
        field_simp [hden.ne']
  have hocc₀ := witness_occupations ht w 0
  have hocc₁ := witness_occupations ht w 1
  simp only [qStar, Fin.sum_univ_two, hocc₀.1, hocc₀.2, hocc₁.1, hocc₁.2, hoverlap₀, hoverlap₁,
    sub_self, mul_zero, zero_add, occupationDefect]
  change Real.sqrt (a * b) * (Real.sqrt (a * b) - (r + Complex.normSq w / (1 + 2 * r))) =
    Real.sqrt (a * b) * (Real.sqrt (a * b) - r - Complex.normSq w / (1 + 2 * r))
  ring

/-- Upper limit for `Complex.normSq w` in the explicit faithful obstruction family. -/
def amplitudeCap (h : ℝ) : ℝ :=
  gibbsLow h * gibbsHigh h * cubicExcess h / (2 + cubicExcess h)

/-- For every positive temperature and every complex coherence in the stated interval, the
faithful, trace-one product witness has both occupations matched and violates the proposed
closure by a strictly positive, explicitly bounded amount. -/
theorem matched_product_obstruction {h : ℝ} (hh : 0 < h) (w : ℂ)
    (hw : 0 < Complex.normSq w) (hcap : Complex.normSq w ≤ amplitudeCap h) :
    let a := gibbsLow h
    let b := gibbsHigh h
    let z := Complex.normSq w
    let ρ := witness a b w
    let D := localGibbs a b ⊗ₖ localGibbs a b
    let margin := cubicExcess h * z / (1 + 2 * Real.sqrt (a * b))
    (localGibbs a b).PosDef ∧ (localGibbs a b).trace = 1 ∧
      (coherentDensity a b w).PosDef ∧ (coherentDensity a b w).trace = 1 ∧
      ρ.PosDef ∧ ρ.trace = 1 ∧
      (∀ k, hole ρ k = a ∧ particle ρ k = b) ∧
      0 < margin ∧ margin ≤ cubicCoefficient h * traceRelativeEntropy ρ D - 4 * qStar ρ := by
  obtain ⟨ha, hab, ht⟩ := gibbs_properties hh
  have hb := ha.trans hab
  have hη := cubicExcess_pos hh
  have hab₀ := mul_pos ha hb
  have hden : 0 < 2 + cubicExcess h := by positivity
  have hlt : Complex.normSq w < gibbsLow h * gibbsHigh h :=
    hcap.trans_lt ((div_lt_iff₀ hden).2 (by nlinarith only [hab₀]))
  have hd := localGibbs_pos ha hb
  have hσ := coherent_pos ht hlt
  have hdt := localGibbs_trace ht
  have hσt := coherent_trace ht w
  dsimp only
  refine ⟨hd, hdt, hσ, hσt, hd.kronecker hσ, ?_, witness_occupations ht w, ?_⟩
  · rw [witness, Matrix.trace_kronecker, hdt, hσt, one_mul]
  · rw [witness_entropy ha hb ht hlt, witness_qStar ha hb ht hlt]
    exact finite_amplitude_obstruction ha hab ht hη hw hcap (cubicCoefficient_mul_entropySlope hh)

/-- Every positive half-gap has a nonempty interval of witness amplitudes, each realized by
an off-diagonal entry of a complex density matrix. -/
theorem amplitude_interval {h : ℝ} (hh : 0 < h) :
    0 < amplitudeCap h ∧
      Set.InjOn (fun z : ℝ => witness (gibbsLow h) (gibbsHigh h) (Real.sqrt z : ℂ))
        (Ioc 0 (amplitudeCap h)) ∧
      ∀ z ∈ Ioc 0 (amplitudeCap h), ∃ w : ℂ,
        Complex.normSq w = z ∧
        let ρ := witness (gibbsLow h) (gibbsHigh h) w
        let D := localGibbs (gibbsLow h) (gibbsHigh h) ⊗ₖ localGibbs (gibbsLow h) (gibbsHigh h)
        ρ.PosDef ∧ ρ.trace = 1 ∧
          4 * qStar ρ < cubicCoefficient h * traceRelativeEntropy ρ D := by
  obtain ⟨ha, hab, _⟩ := gibbs_properties hh
  have hb := ha.trans hab
  have hη := cubicExcess_pos hh
  refine ⟨by unfold amplitudeCap; positivity, ?_, ?_⟩
  · intro z hz y hy hzy
    have hentry := congrArg (fun ρ : TwoMode => ρ (0, 0) (0, 1)) hzy
    simp only [witness, Matrix.kroneckerMap_apply, localGibbs, Matrix.diagonal_apply_eq,
      occupations, Matrix.cons_val_zero, coherentDensity, Matrix.of_apply,
      Matrix.cons_val_one] at hentry
    have hnonzero : (gibbsLow h : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hroot := congrArg Complex.re (mul_left_cancel₀ hnonzero hentry)
    exact (Real.sqrt_inj hz.1.le hy.1.le).mp hroot
  intro z hz
  let w : ℂ := (Real.sqrt z : ℝ)
  have hw : Complex.normSq w = z := by
    change Complex.normSq (Real.sqrt z : ℂ) = z
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt hz.1.le]
  have hphys := matched_product_obstruction hh w
    (show 0 < Complex.normSq w by rw [hw]; exact hz.1)
    (show Complex.normSq w ≤ amplitudeCap h by rw [hw]; exact hz.2)
  dsimp only at hphys
  obtain ⟨_, _, _, _, hp, htr, _, hmargin, hgap⟩ := hphys
  exact ⟨w, hw, hp, htr, sub_pos.mp (hmargin.trans_le hgap)⟩

end Physical

end D5.S3.Quantum.Semigroups.WuCubicOccupationEntropyObstruction
