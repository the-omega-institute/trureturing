/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual zero spectra and oriented primitives for real root cutoffs. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHRootCorrection

/-! Actual zero spectra and oriented primitives for real root cutoffs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

private lemma weighted_zero_mode (r u : ℝ) (k : ℕ) :
    (Real.exp ((1 - r) * u) : ℂ) * mode 1 u k = mode r u k := by
  rw [mode, mode, mul_left_comm, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma weighted_zero_tail {r : ℝ} (hr : 1 < r) (v : ℝ) :
    let f := fun s : ℝ => (s ^ (-r : ℝ)) • zeroTail (Real.log s)
    IntegrableOn f (Ioi (Real.exp v)) ∧
      HasSum (fun k : ℕ => mode r v k / ((r : ℂ) - actualZero k))
        (∫ s in Ioi (Real.exp v), f s) := by
  dsimp only
  let f (s : ℝ) := (s ^ (-r : ℝ)) • zeroTail (Real.log s)
  have he (u : ℝ) : Real.exp u • f (Real.exp u) = ∑' k : ℕ, mode r u k := by
    change Real.exp u • ((Real.exp u ^ (-r : ℝ)) • zeroTail (Real.log (Real.exp u))) = _
    simp only [Real.log_exp, smul_smul, ← Real.exp_mul, ← Real.exp_add]
    rw [show u + u * (-r) = (1 - r) * u by ring, Complex.real_smul, zeroTail, ← tsum_mul_left]
    exact tsum_congr (weighted_zero_mode r u)
  let weight (u : ℝ) := Real.exp (max 0 (-v)) * Real.exp ((1 - r) * u)
  let mass := ∑' k : ℕ, ‖actualCoeff k‖
  have hweight : IntegrableOn weight (Ioi v) := by
    have h : IntegrableOn (fun u : ℝ => Real.exp ((1 - r) * u)) (Ioi v) := by
      exact integrableOn_exp_mul_Ioi (a := 1 - r) (by linarith) v
    exact h.const_mul (Real.exp (max 0 (-v)))
  have hbound (u : ℝ) (hu : v < u) (k : ℕ) :
      ‖mode r u k‖ ≤ ‖actualCoeff k‖ * weight u := by
    rw [norm_mode]
    dsimp only [weight]
    rw [← Real.exp_add]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    by_cases hu0 : 0 ≤ u
    · nlinarith [mul_nonneg (sub_nonneg.mpr (zero_re_lt_one k).le) hu0, le_max_left 0 (-v)]
    · have h := mul_nonpos_of_nonneg_of_nonpos (zero_re_pos k).le (le_of_not_ge hu0)
      linarith [le_max_right 0 (-v)]
  have hae : ∀ᵐ u ∂volume.restrict (Ioi v), v < u :=
    ae_restrict_mem measurableSet_Ioi
  have hintegrable : IntegrableOn (fun u => Real.exp u • f (Real.exp u)) (Ioi v) := by
    apply (hweight.const_mul mass).mono'
    · have heq : (fun u => Real.exp u • f (Real.exp u)) =
          fun u => Real.exp ((1 - r) * u) • zeroTail u := by
        funext u
        change Real.exp u • ((Real.exp u ^ (-r : ℝ)) • zeroTail (Real.log (Real.exp u))) = _
        simp only [Real.log_exp, smul_smul, ← Real.exp_mul, ← Real.exp_add]
        rw [show u + u * (-r) = (1 - r) * u by ring]
      rw [heq]
      exact ((by fun_prop : Continuous (fun u : ℝ => Real.exp ((1 - r) * u))).smul
        zeroTail_continuous).aestronglyMeasurable
    · filter_upwards [hae] with u hu
      rw [he]
      exact tsum_of_norm_bounded ((actualCoeff_hasSum.summable.norm.hasSum).mul_right _)
        (hbound u hu)
  refine ⟨(integrableOn_comp_exp_Ioi f v).mp hintegrable, ?_⟩
  rw [← integral_comp_exp_Ioi f v]
  have hsum : HasSum (fun k : ℕ => ∫ u in Ioi v, mode r u k)
      (∫ u in Ioi v, Real.exp u • f (Real.exp u)) := by
    apply hasSum_integral_of_dominated_convergence
      (fun k u => ‖actualCoeff k‖ * weight u)
    · intro k
      exact (show Continuous (fun u => mode r u k) by unfold mode; fun_prop).aestronglyMeasurable
    · intro k
      filter_upwards [hae] with u hu using hbound u hu k
    · exact ae_of_all _ fun u => actualCoeff_hasSum.summable.norm.mul_right _
    · simpa only [tsum_mul_right] using hweight.const_mul mass
    · exact ae_of_all _ fun u => (he u).symm ▸ (mode_summable r u).hasSum
  convert hsum using 1
  funext k
  have hneg : (actualZero k - (r : ℂ)).re < 0 := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith [zero_re_lt_one k]
  simp only [mode, integral_const_mul,
    integral_exp_mul_complex_Ioi hneg]
  rw [show (r : ℂ) - actualZero k = -(actualZero k - (r : ℂ)) by ring, div_neg]
  ring

def rootCoeff (r : ℝ) (k : ℕ) : ℂ :=
  -(r : ℂ) / (actualZero k * ((r : ℂ) - actualZero k))

def rootMode (r u : ℝ) (k : ℕ) : ℂ :=
  rootCoeff r k * Complex.exp ((actualZero k / (r : ℂ) - 1 / 2) * (u : ℂ))

def rootDensity (r u : ℝ) : ℝ := (∑' k, rootMode r u k).re

theorem root_spectral_transform {r : ℝ} (hr : 1 < r) (v : ℝ) :
    let y := Real.exp v
    r * Real.exp ((1 - r / 2) * v) * (-(zeroTail (Real.log y)).re +
      (r - 1) * Real.exp ((r - 1) * v) *
        (∫ s in Ioi y, s ^ (-r) * (zeroTail (Real.log s)).re)) = rootDensity r (r * v) := by
  dsimp only
  let y := Real.exp v
  let t := Real.exp ((r - 1) * v)
  let d := -r * Real.exp ((1 - r / 2) * v)
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hr).ne'
  obtain ⟨hi, hs⟩ := weighted_zero_tail hr v
  have hre : (∫ s in Ioi y, s ^ (-r) * (zeroTail (Real.log s)).re) =
      (∫ s in Ioi y, (s ^ (-r)) • zeroTail (Real.log s)).re := by
    have h := integral_re hi
    change (∫ s in Ioi (Real.exp v), ((s ^ (-r : ℝ)) • zeroTail (Real.log s)).re) =
      (∫ s in Ioi (Real.exp v), (s ^ (-r : ℝ)) • zeroTail (Real.log s)).re at h
    simpa only [Complex.real_smul, Complex.re_ofReal_mul] using h
  rw [hre, Real.log_exp]
  have hterms := ((mode_summable 1 v).hasSum.sub
    (hs.mul_left (((r - 1) * t : ℝ) : ℂ))).mul_left (d : ℂ)
  have he (k : ℕ) : (t : ℂ) * mode r v k = mode 1 v k := by
    rw [mode, mode, mul_left_comm, show (t : ℂ) = Complex.exp (((r - 1) * v : ℝ) : ℂ) by
      rw [← Complex.ofReal_exp], ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hcoef (k : ℕ) : rootCoeff r k =
      -(r : ℂ) * (actualCoeff k - ((r : ℂ) - 1) * (actualCoeff k / ((r : ℂ) - actualZero k))) := by
    have h0 : actualZero k ≠ 0 := by
      intro h
      simpa [h] using zero_re_pos k
    have h1 : 1 - actualZero k ≠ 0 := by
      intro h
      have heq := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at heq
      linarith [zero_re_lt_one k]
    have h2 : (r : ℂ) - actualZero k ≠ 0 := by
      intro h
      have heq := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at heq
      linarith [zero_re_lt_one k]
    unfold rootCoeff actualCoeff
    field_simp
    ring
  have hmatch (k : ℕ) : (d : ℂ) * (mode 1 v k -
      (((r - 1) * t : ℝ) : ℂ) * (mode r v k / ((r : ℂ) - actualZero k))) =
      rootMode r (r * v) k := by
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
    rw [mul_assoc ((r : ℂ) - 1), ← mul_div_assoc, he]
    unfold rootMode d
    rw [hcoef, mode]
    push_cast
    have h_exp : Complex.exp (((1 : ℂ) - (r : ℂ) / 2) * (v : ℂ)) *
        Complex.exp ((actualZero k - 1) * (v : ℂ)) =
        Complex.exp ((actualZero k / (r : ℂ) - 1 / 2) * ((r : ℂ) * (v : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      field_simp
      ring
    rw [← h_exp]
    ring
  have hts := congrArg Complex.re hterms.tsum_eq
  simp only [hmatch] at hts
  change rootDensity r (r * v) =
    ((d : ℂ) * (zeroTail v - (((r - 1) * t : ℝ) : ℂ) *
      (∫ s in Ioi y, (s ^ (-r)) • zeroTail (Real.log s)))).re at hts
  rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.re_ofReal_mul] at hts
  rw [hts]
  dsimp only [d, t, y]
  ring

private def rootExponent (r : ℝ) (k : ℕ) : ℂ :=
  actualZero k / (r : ℂ) - 1 / 2

def rootPrimitive (r x : ℝ) : ℝ :=
  (∑' k : ℕ, (2 * (r : ℂ)^2) * (x : ℂ) ^ (rootExponent r k) /
    (actualZero k * ((r : ℂ) - actualZero k) *
      ((r : ℂ) - 2 * actualZero k))).re

private lemma rootExponent_re_bound {r : ℝ} (hr : 1 < r) (k : ℕ) :
    |(rootExponent r k).re| ≤ 1 / 2 := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have he : (rootExponent r k).re = (actualZero k).re / r - 1 / 2 := by
    simp [rootExponent, Complex.div_re, Complex.normSq_ofReal]
    field_simp
  rw [he, abs_le]
  constructor
  · linarith [div_nonneg (zero_re_pos k).le hr0.le]
  · linarith [(div_le_one₀ hr0).mpr (by linarith [zero_re_lt_one k] : (actualZero k).re ≤ r)]

private lemma rootExponent_norm {r : ℝ} (hr : 1 < r) (k : ℕ) :
    r⁻¹ ≤ ‖rootExponent r k‖ := by
  have hh : 10 < |(actualZero k).im| :=
    actual_height_gt_ten _ (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)
  have hr0 : 0 < r := zero_lt_one.trans hr
  have he : (rootExponent r k).im = (actualZero k).im / r := by
    simp [rootExponent, Complex.div_im, Complex.normSq_ofReal]
    field_simp
  calc
    _ ≤ |(rootExponent r k).im| := by
      rw [he, abs_div, abs_of_pos hr0, ← one_div]
      exact div_le_div_of_nonneg_right (by linarith) hr0.le
    _ ≤ _ := Complex.abs_im_le_norm _

lemma rootCoeff_bound {r : ℝ} (hr : 1 < r) (k : ℕ) :
    ‖rootCoeff r k‖ ≤ r * ‖actualCoeff k‖ := by
  have hgap : ‖1 - actualZero k‖ ≤ ‖(r : ℂ) - actualZero k‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    apply Real.sqrt_le_sqrt
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [mul_nonneg (sub_nonneg.mpr hr.le)
      (show 0 ≤ r + 1 - 2 * (actualZero k).re by linarith [zero_re_lt_one k])]
  have hgap0 : 0 < ‖1 - actualZero k‖ := by
    apply norm_pos_iff.mpr
    intro h
    have heq := congrArg Complex.re h
    simp at heq
    linarith [zero_re_lt_one k]
  unfold rootCoeff actualCoeff
  simp only [norm_div, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_one]
  rw [abs_of_pos (zero_lt_one.trans hr)]
  rw [← mul_div_assoc, mul_one]
  apply div_le_div_of_nonneg_left (zero_lt_one.trans hr).le (mul_pos (norm_pos_iff.mpr ?_) hgap0)
    (mul_le_mul_of_nonneg_left hgap (norm_nonneg _))
  intro h
  simpa [h] using zero_re_pos k

private lemma rootMode_bound {r a b u : ℝ} (hr : 1 < r) (hu : u ∈ uIcc a b) (k : ℕ) :
    ‖rootMode r u k‖ ≤ (r * ‖actualCoeff k‖) * Real.exp (max |a| |b| / 2) := by
  have habs : |u| ≤ max |a| |b| := by
    rw [abs_le]
    exact ⟨le_trans (le_min (by linarith [neg_le_abs a, le_max_left |a| |b|])
      (by linarith [neg_le_abs b, le_max_right |a| |b|])) hu.1,
      hu.2.trans (max_le
        ((le_abs_self a).trans (le_max_left _ _))
        ((le_abs_self b).trans (le_max_right _ _)))⟩
  change ‖rootCoeff r k * Complex.exp (rootExponent r k * (u : ℂ))‖ ≤ _
  rw [norm_mul, Complex.norm_exp, mul_comm (rootExponent r k), Complex.re_ofReal_mul]
  refine mul_le_mul (rootCoeff_bound hr k) (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _) (by positivity)
  calc
    _ ≤ |u * (rootExponent r k).re| := le_abs_self _
    _ = |u| * |(rootExponent r k).re| := abs_mul _ _
    _ ≤ _ := by
      have h := mul_le_mul habs (rootExponent_re_bound hr k) (abs_nonneg _) (by positivity)
      simpa only [mul_one_div] using h

private lemma rootMode_summable {r : ℝ} (hr : 1 < r) (u : ℝ) :
    Summable (fun k => rootMode r u k) :=
  ((actualCoeff_hasSum.summable.norm.mul_left r).mul_right
    (Real.exp (max |u| |u| / 2))).of_norm_bounded
      (rootMode_bound hr (show u ∈ uIcc u u by simp))

private lemma rootPrimitiveMode_summable {r : ℝ} (hr : 1 < r) (u : ℝ) :
    Summable (fun k => rootMode r u k / rootExponent r k) := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  apply (((actualCoeff_hasSum.summable.norm.mul_left r).mul_right
    (Real.exp (max |u| |u| / 2))).mul_right r).of_norm_bounded
  intro k
  rw [norm_div]
  have hnorm := rootExponent_norm hr k
  calc
    _ ≤ ‖rootMode r u k‖ / r⁻¹ :=
      div_le_div_of_nonneg_left (norm_nonneg _) (inv_pos.mpr hr0) hnorm
    _ = ‖rootMode r u k‖ * r := by rw [div_inv_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (rootMode_bound hr (show u ∈ uIcc u u by simp) k) hr0.le

private lemma rootPrimitiveMode_eq {r : ℝ} (hr : 1 < r) (u : ℝ) (k : ℕ) :
    rootMode r u k / rootExponent r k =
      (2 * (r : ℂ)^2) * (Real.exp u : ℂ) ^ (rootExponent r k) /
        (actualZero k * ((r : ℂ) - actualZero k) * ((r : ℂ) - 2 * actualZero k)) := by
  have hp : (Real.exp u : ℂ) ^ (rootExponent r k) =
      Complex.exp (rootExponent r k * (u : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    rw [mul_comm]
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hr).ne'
  change rootCoeff r k * Complex.exp (rootExponent r k * (u : ℂ)) / rootExponent r k = _
  have h0 : actualZero k ≠ 0 := by
    intro hz
    simpa [hz] using zero_re_pos k
  have h1 : (r : ℂ) - actualZero k ≠ 0 := by
    intro hz
    have he := congrArg Complex.re hz
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at he
    linarith [zero_re_lt_one k]
  have h2 : (r : ℂ) - 2 * actualZero k ≠ 0 := by
    intro hz
    have he := congrArg Complex.im hz
    norm_num [Complex.mul_im] at he
    have hh := actual_height_gt_ten _ (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)
    have hzero : (actualZero k).im = 0 := by linarith
    change 10 < |(actualZero k).im| at hh
    simp [hzero] at hh
    linarith only [hh]
  have he : rootExponent r k = -(((r : ℂ) - 2 * actualZero k) / (2 * (r : ℂ))) := by
    unfold rootExponent
    field_simp
    ring
  rw [hp, rootCoeff, he]
  field_simp

theorem root_density_integral {r : ℝ} (hr : 1 < r) (a b : ℝ) :
    IntervalIntegrable (rootDensity r) volume a b ∧
      (∫ u in a..b, rootDensity r u) =
        rootPrimitive r (Real.exp b) - rootPrimitive r (Real.exp a) := by
  let series (u : ℝ) := ∑' k, rootMode r u k
  let bound (k : ℕ) := (r * ‖actualCoeff k‖) * Real.exp (max |a| |b| / 2)
  have hs : Summable bound := (actualCoeff_hasSum.summable.norm.mul_left r).mul_right _
  have hc (k : ℕ) : Continuous (fun u => rootMode r u k) := by unfold rootMode; fun_prop
  have hcont : ContinuousOn series (uIcc a b) := by
    exact continuousOn_tsum (fun k => (hc k).continuousOn) hs (fun k u hu => rootMode_bound hr hu k)
  refine ⟨(Complex.continuous_re.comp_continuousOn hcont).intervalIntegrable, ?_⟩
  have hre : (∫ u in a..b, rootDensity r u) = (∫ u in a..b, series u).re := by
    change (∫ u in a..b, (series u).re) = _
    exact intervalIntegral.intervalIntegral_re hcont.intervalIntegrable
  have hi : HasSum (fun k => ∫ u in a..b, rootMode r u k) (∫ u in a..b, series u) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => bound k)
    · intro k
      exact (hc k).aestronglyMeasurable
    · intro k
      exact ae_of_all _ fun u hu => rootMode_bound hr ⟨hu.1.le, hu.2⟩ k
    · exact ae_of_all _ fun _ _ => hs
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun u _ => (rootMode_summable hr u).hasSum
  have hmode (k : ℕ) : (∫ u in a..b, rootMode r u k) =
      rootMode r b k / rootExponent r k - rootMode r a k / rootExponent r k := by
    have hn : rootExponent r k ≠ 0 := norm_pos_iff.mp
      ((inv_pos.mpr (zero_lt_one.trans hr)).trans_le (rootExponent_norm hr k))
    change (∫ u in a..b, rootCoeff r k * Complex.exp (rootExponent r k * (u : ℂ))) =
      rootCoeff r k * Complex.exp (rootExponent r k * (b : ℂ)) / rootExponent r k -
      rootCoeff r k * Complex.exp (rootExponent r k * (a : ℂ)) / rootExponent r k
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hn]
    ring
  rw [hre, ← hi.tsum_eq, tsum_congr hmode, (rootPrimitiveMode_summable hr b).tsum_sub
    (rootPrimitiveMode_summable hr a), Complex.sub_re]
  simp_rw [rootPrimitiveMode_eq hr, rootPrimitive]

theorem root_centered_error {r : ℝ} (hr : 1 < r)
    {v : ℝ} (hv : Real.log 2 ≤ v) :
    |centered r (Real.exp (r * v)) - rootDensity r (r * v)| ≤
      (2 * r - 1) * C * Real.exp (-(r * v) / 2) := by
  let y := Real.exp v
  let x := Real.exp (r * v)
  let s := Real.exp ((1 - r / 2) * v)
  let w := Real.exp ((r - 1) * v)
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hx0 : 0 < x := Real.exp_pos _
  have hv0 : 0 ≤ v := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hv
  have hx1 : 1 ≤ x := (Real.exp_zero : Real.exp (0 : ℝ) = 1) ▸
    Real.exp_le_exp.mpr (mul_nonneg hr0.le hv0)
  have hy : 2 ≤ y := by
    simpa [y, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hv
  have hy0 : 0 < y := Real.exp_pos _
  have hroot : x ^ r⁻¹ = y := by
    dsimp only [x, y]
    rw [← Real.exp_mul]
    congr 1
    field_simp
  have hscale₁ : Real.sqrt x * y ^ (1 - r) = s := by
    rw [Real.sqrt_eq_rpow]
    dsimp only [x, y, s]
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  have hscale₂ : s * w = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    dsimp only [s, w, x]
    rw [← Real.exp_add, ← Real.exp_mul]
    congr 1
    ring
  have hdecay : s * y⁻¹ = Real.exp (-(r * v) / 2) := by
    dsimp only [s, y]
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have hcut := centered_root_tail (r := r) hr.le (zero_lt_one.trans_le hx1)
  dsimp only at hcut
  change centered r x = _ at hcut
  rw [hroot] at hcut
  have h := root_spectral_transform hr v
  dsimp only at h
  change r * s * (-(zeroTail (Real.log y)).re + (r - 1) * w *
      (∫ t in Ioi y, t ^ (-r) * (zeroTail (Real.log t)).re)) = _ at h
  obtain ⟨he, hb⟩ := weighted_bound (f := qError) (b := r) (d := 1) hy (by linarith)
    (q_continuous.add z_continuous) (fun _ ht => qError_bound ht)
  have hZ := (weighted_zero_tail hr v).1
  have hz : IntegrableOn (fun t => t ^ (-r) * (zeroTail (Real.log t)).re) (Ioi y) := by
    have hRe := hZ.re
    change IntegrableOn (fun t : ℝ => ((t ^ (-r)) • zeroTail (Real.log t)).re) (Ioi y) at hRe
    simpa only [Complex.real_smul, Complex.re_ofReal_mul] using hRe
  have hsplit : (∫ t in Ioi y, t ^ (-r) * Q t) =
      (∫ t in Ioi y, t ^ (-r) * qError t) -
        (∫ t in Ioi y, t ^ (-r) * (zeroTail (Real.log t)).re) := by
    rw [← integral_sub (f := fun t => t ^ (-r) * qError t)
      (g := fun t => t ^ (-r) * (zeroTail (Real.log t)).re) he hz]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by unfold qError; ring)
  have hdiff : centered r x - rootDensity r (r * v) =
      r * s * (qError y - (r - 1) * w * (∫ t in Ioi y, t ^ (-r) * qError t)) := by
    rw [hcut, ← h, hsplit]
    change _ = r * s * (Q y + (zeroTail (Real.log y)).re - (r - 1) * w *
      (∫ t in Ioi y, t ^ (-r) * qError t))
    linear_combination r * Q y * hscale₁ + r * (r - 1) *
      ((∫ t in Ioi y, t ^ (-r) * qError t) -
        (∫ t in Ioi y, t ^ (-r) * (zeroTail (Real.log t)).re)) * hscale₂
  have hs0 : 0 < s := Real.exp_pos _
  have hw0 : 0 < w := Real.exp_pos _
  have hweight : w * y ^ (-r) = y⁻¹ := by
    dsimp only [w, y]
    rw [← Real.exp_mul, ← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  have hb' : |∫ t in Ioi y, t ^ (-r) * qError t| ≤ C / r * y ^ (-r) := by
    simpa only [show r + 1 - 1 = r by ring, show 1 - (r + 1) = -r by ring] using hb
  change |centered r x - rootDensity r (r * v)| ≤ _
  rw [hdiff, abs_mul, abs_of_nonneg (mul_nonneg hr0.le hs0.le)]
  calc
    _ ≤ r * s * (|qError y| + (r - 1) * w * |∫ t in Ioi y, t ^ (-r) * qError t|) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hr0.le hs0.le)
      exact (abs_sub _ _).trans_eq (by rw [abs_mul,
        abs_of_nonneg (mul_nonneg (by linarith) hw0.le)])
    _ ≤ r * s * (C * y⁻¹ + (r - 1) * w * (C / r * y ^ (-r))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hr0.le hs0.le)
      rw [← Real.rpow_neg_one]
      exact add_le_add (qError_bound hy) (mul_le_mul_of_nonneg_left hb'
        (mul_nonneg (by linarith) hw0.le))
    _ = _ := by
      rw [show (r - 1) * w * (C / r * y ^ (-r)) = (r - 1) * (C / r) *
        (w * y ^ (-r)) by ring, hweight, ← hdecay]
      field_simp
      ring

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
