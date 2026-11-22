/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootSignalCusp
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootSignalCusp
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A logarithmic cusp with a quadratic remainder for the symmetric root spectrum. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusEvenCutoffShrinkingWidth
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelGlobalStrictPositivity
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The even phase difference transfers the local arithmetic kernel expansion to the root series. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff actualCoeff_hasSum)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower (rootCoeff rootCoeff_bound)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean (frequency frequency_real)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (coeff_real on_line)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity (K K_zero K_zero_pos)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp (c R cusp_remainder_bound)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelGlobalStrictPositivity (actual_cosine_hasSum weight)

private theorem coefficient_correction (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r)
    (k : ℕ) :
    (rootCoeff r k).re + r * weight k =
      r * (r - 1) * (r - 1 / 2) * weight k /
        ((r - 1 / 2) ^ 2 + (actualZero k).im ^ 2) := by
  have hzero : actualZero k ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [on_line hRH k] at this
  have hone : 1 - actualZero k ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num [Complex.sub_re, on_line hRH k] at this
  have hgap : (r : ℂ) - actualZero k ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, on_line hRH k, Complex.zero_re] at this
    linarith
  have hdiff : rootCoeff r k + (r : ℂ) * actualCoeff k =
      ((r * (r - 1) * weight k : ℝ) : ℂ) / ((r : ℂ) - actualZero k) := by
    rw [show ((r * (r - 1) * weight k : ℝ) : ℂ) =
      (r : ℂ) * ((r : ℂ) - 1) * actualCoeff k by
        simp only [coeff_real hRH k, weight, Complex.ofReal_mul, Complex.ofReal_sub,
          Complex.ofReal_one]]
    unfold rootCoeff actualCoeff
    field_simp [hzero, hone, hgap]
    ring
  have hre := congrArg Complex.re hdiff
  simp only [Complex.add_re, Complex.re_ofReal_mul, coeff_real hRH k, Complex.ofReal_re,
    Complex.div_re, Complex.ofReal_im, zero_mul, zero_div, add_zero, Complex.sub_re,
    Complex.sub_im, zero_sub, Complex.normSq_apply, neg_mul_neg, on_line hRH k, ← pow_two,
    weight] at hre
  unfold weight
  rw [hre]
  ring

private theorem phase_eq (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r) (u : ℝ) (k : ℕ) :
    frequency k / (r : ℂ) * (u : ℂ) = (((actualZero k).im * (u / r) : ℝ) : ℂ) * Complex.I := by
  have hfreq : frequency k = ((actualZero k).im : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [frequency_real hRH k, Complex.mul_re]
    · simp [frequency, Complex.sub_im, Complex.mul_im]
  rw [hfreq]
  push_cast
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  field_simp

private theorem root_series_hasSum (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r) (u : ℝ) :
    HasSum (fun k => (rootCoeff r k * Complex.exp (frequency k / (r : ℂ) * (u : ℂ))).re)
      ((∑' k, rootCoeff r k * Complex.exp (frequency k / (r : ℂ) * (u : ℂ))).re) := by
  apply Complex.hasSum_re
  apply Summable.hasSum
  apply Summable.of_norm_bounded (actualCoeff_hasSum.summable.norm.mul_left r)
  intro k
  rw [phase_eq hRH hr u k, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact rootCoeff_bound hr k

private theorem cosine_difference_hasSum (hRH : RiemannHypothesis) (t : ℝ) :
    HasSum (fun k => 2 * (Real.cos ((actualZero k).im * t) - 1) * weight k)
      (2 * (K t - K 0)) := by
  have hd := ((Complex.hasSum_re (actual_cosine_hasSum hRH t)).sub
    (Complex.hasSum_re (actual_cosine_hasSum hRH 0))).mul_left (2 : ℝ)
  convert hd using 1
  · funext k
    simp only [Complex.ofReal_re, mul_zero, Real.cos_zero, mul_one, weight]
    ring

private theorem symmetric_difference_hasSum (hRH : RiemannHypothesis) {r : ℝ}
    (hr : 1 < r) (h : ℝ) :
    HasSum (fun k => 2 * (Real.cos ((actualZero k).im * (h / r)) - 1) * (rootCoeff r k).re)
      ((1 / 2 - (2 * r)⁻¹) *
        (rootSignal r h + rootSignal r (-h) - 2 * rootSignal r 0)) := by
  have hs : 0 < 1 / 2 - (2 * r)⁻¹ := by
    rw [inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by linarith)).2 (by linarith)
  have hd := ((root_series_hasSum hRH hr h).add (root_series_hasSum hRH hr (-h))).sub
    ((root_series_hasSum hRH hr 0).mul_left (2 : ℝ))
  convert hd using 1
  · funext k
    simp only [phase_eq hRH hr, neg_div, mul_neg, Real.cos_neg, Real.sin_neg,
      mul_zero, Complex.ofReal_zero, Complex.exp_zero, mul_one,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.mul_re]
    ring
  · unfold rootSignal
    rw [← add_div, ← mul_div_assoc, ← sub_div, mul_div_cancel₀ _ hs.ne']

private theorem symmetric_kernel_error (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r)
    (h : ℝ) :
    |(1 / 2 - (2 * r)⁻¹) * (rootSignal r h + rootSignal r (-h) - 2 * rootSignal r 0) +
        2 * r * (K (h / r) - K 0)| ≤
      r * (r - 1) * (r - 1 / 2) * firstLiMass * (h / r) ^ 2 := by
  have hw : HasSum weight firstLiMass := by
    unfold weight
    simpa only [coeff_real hRH, Complex.ofReal_re] using
      Complex.hasSum_re actualCoeff_hasSum
  let b := r * (r - 1) * (r - 1 / 2)
  let t := h / r
  have hr0 : 0 < r := by linarith
  have hra : 0 < r - 1 / 2 := by linarith
  have hr1 : 0 ≤ r - 1 := sub_nonneg.mpr hr.le
  have hb : 0 ≤ b := mul_nonneg (mul_nonneg hr0.le hr1) hra.le
  have hmajor := hw.mul_left (b * t ^ 2)
  have hsum := (symmetric_difference_hasSum hRH hr h).add
    ((cosine_difference_hasSum hRH t).mul_left r)
  have hbound (k : ℕ) :
      |2 * (Real.cos ((actualZero k).im * t) - 1) * (rootCoeff r k).re +
        r * (2 * (Real.cos ((actualZero k).im * t) - 1) * weight k)| ≤
        (b * t ^ 2) * weight k := by
    let ordinate := (actualZero k).im
    let denom := (r - 1 / 2) ^ 2 + ordinate ^ 2
    have hd : 0 < denom := add_pos_of_pos_of_nonneg (sq_pos_of_pos hra) (sq_nonneg _)
    have hwk : 0 ≤ weight k := by unfold weight; positivity
    have phase_bound : |2 * (Real.cos (ordinate * t) - 1)| ≤ (ordinate * t) ^ 2 := by
      rw [abs_of_nonpos (by linarith [Real.cos_le_one (ordinate * t)])]
      linarith [Real.one_sub_sq_div_two_le_cos (x := ordinate * t)]
    rw [show _ + _ = 2 * (Real.cos (ordinate * t) - 1) *
        ((rootCoeff r k).re + r * weight k) by dsimp [ordinate]; ring,
      coefficient_correction hRH hr, abs_mul]
    change _ * |b * weight k / denom| ≤ _
    rw [abs_of_nonneg (div_nonneg (mul_nonneg hb hwk) hd.le)]
    calc
      _ ≤ (ordinate * t) ^ 2 * (b * weight k / denom) :=
        mul_le_mul_of_nonneg_right phase_bound (by positivity)
      _ = (ordinate ^ 2 / denom) * (b * t ^ 2 * weight k) := by ring
      _ ≤ 1 * (b * t ^ 2 * weight k) :=
        mul_le_mul_of_nonneg_right
          ((div_le_one hd).2 (le_add_of_nonneg_left (sq_nonneg _)))
          (mul_nonneg (mul_nonneg hb (sq_nonneg _)) hwk)
      _ = _ := one_mul _
  have hexpand : r * (2 * (K t - K 0)) = 2 * r * (K t - K 0) := by ring
  rw [hexpand] at hsum
  rw [← hsum.tsum_eq, show r * (r - 1) * (r - 1 / 2) * firstLiMass * (h / r) ^ 2 =
    b * t ^ 2 * firstLiMass by dsimp [b, t]; ring, ← hmajor.tsum_eq]
  rw [← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm (hsum.summable.norm)).trans
    (hsum.summable.norm.tsum_le_tsum (fun k => by simpa only [Real.norm_eq_abs] using hbound k)
      hmajor.summable)

/-- On RH, the symmetric difference of the full centered root spectrum has a logarithmic cusp. -/
theorem root_signal_symmetric_cusp (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r) :
    let s : ℝ := 1 / 2 - (2 * r)⁻¹
    ∃ C > 0, ∀ h : ℝ, 0 < h → h ≤ r / 2 →
      |rootSignal r h + rootSignal r (-h) - 2 * rootSignal r 0 -
        (h / s) * (Real.log (1 / h) + Real.log r - 2 * c)| ≤ C * h ^ 2 := by
  dsimp only
  let s : ℝ := 1 / 2 - (2 * r)⁻¹
  change ∃ C > 0, ∀ h : ℝ, 0 < h → h ≤ r / 2 →
    |rootSignal r h + rootSignal r (-h) - 2 * rootSignal r 0 -
      (h / s) * (Real.log (1 / h) + Real.log r - 2 * c)| ≤ C * h ^ 2
  have hr0 : 0 < r := by linarith
  have hs : 0 < s := by
    dsimp [s]
    rw [inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by positivity)).2 (by linarith)
  have hm : 0 < firstLiMass := K_zero ▸ K_zero_pos
  have hr1 : 0 ≤ r - 1 := sub_nonneg.mpr hr.le
  have hra : 0 ≤ r - 1 / 2 := by linarith
  have hnum := mul_nonneg (mul_nonneg hr1 hra) hm.le
  refine ⟨(4 + (r - 1) * (r - 1 / 2) * firstLiMass) / (r * s),
    div_pos (by linarith) (mul_pos hr0 hs), ?_⟩
  intro h hh hh'
  let t := h / r
  have ht : 0 < t := div_pos hh hr0
  have ht' : t ≤ 1 / 2 := (div_le_iff₀ hr0).2 (by linarith)
  have hlog : Real.log (1 / h) + Real.log r = -Real.log t := by
    rw [one_div, Real.log_inv, Real.log_div hh.ne' hr0.ne']
    ring
  have hscale : r * t = h := by dsimp [t]; field_simp
  have hid :
      rootSignal r h + rootSignal r (-h) - 2 * rootSignal r 0 -
        (h / s) * (Real.log (1 / h) + Real.log r - 2 * c) =
      ((s * (rootSignal r h + rootSignal r (-h) - 2 * rootSignal r 0) +
        2 * r * (K t - K 0)) - 2 * r * R t) / s := by
    rw [hlog, R, K_zero, eq_div_iff hs.ne']
    rw [sub_mul, mul_right_comm (h / s), div_mul_cancel₀ _ hs.ne']
    linear_combination -(Real.log t + 2 * c) * hscale
  rw [hid, abs_div, abs_of_pos hs]
  apply (div_le_iff₀ hs).2
  calc
    _ ≤ |s * (rootSignal r h + rootSignal r (-h) - 2 * rootSignal r 0) +
        2 * r * (K t - K 0)| + |2 * r * R t| := abs_sub _ _
    _ ≤ r * (r - 1) * (r - 1 / 2) * firstLiMass * t ^ 2 + (2 * r) * (2 * t ^ 2) := by
      apply add_le_add (symmetric_kernel_error hRH hr h)
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * r)]
      exact mul_le_mul_of_nonneg_left (cusp_remainder_bound ht ht') (by positivity)
    _ = _ := by
      dsimp [t]
      field_simp [hr0.ne', hs.ne']
      ring

#print axioms root_signal_symmetric_cusp

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
