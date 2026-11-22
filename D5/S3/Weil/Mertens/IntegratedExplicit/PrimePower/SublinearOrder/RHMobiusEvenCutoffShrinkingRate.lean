/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffShrinkingRate
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffShrinkingRate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A logarithmic-square modulus for the centered root spectrum. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusEvenCutoff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The truncated reciprocal moment and inverse-square tail bound all small phase shifts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open D5.S3.Weil.Mertens.ZeroAbscissaPower (actual_zero actual_low_weight actual_high_weight)
open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff actualCoeff_hasSum)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean (frequency frequency_real)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

private theorem root_coeff_frequency_bound {r : ℝ} (hr : 0 < r) (k : ℕ) :
    ‖rootCoeff r k‖ * |(actualZero k).im| ≤ r / ‖actualZero k‖ ∧
    ‖rootCoeff r k‖ ≤ r * ((actualZero k).im)⁻¹ ^ 2 := by
  let z := actualZero k
  let height := |z.im|
  have hp : 0 < height :=
    (by norm_num : (0 : ℝ) < 10).trans (actual_height_gt_ten z (actual_zero k))
  have ha : height ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hb : height ≤ ‖(r : ℂ) - z‖ := by
    simpa only [height, Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] using
      Complex.abs_im_le_norm ((r : ℂ) - z)
  have hbound : ‖rootCoeff r k‖ ≤ (r / ‖z‖) / height := by
    change ‖-(r : ℂ) / (z * ((r : ℂ) - z))‖ ≤ _
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, norm_mul,
      div_div]
    exact div_le_div_of_nonneg_left hr.le (mul_pos (hp.trans_le ha) hp)
      (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  refine ⟨(le_div_iff₀ hp).mp hbound, hbound.trans ?_⟩
  have h := div_le_div_of_nonneg_right (div_le_div_of_nonneg_left hr.le hp ha) hp.le
  refine h.trans (le_of_eq ?_)
  rw [div_div, ← sq, show height ^ 2 = z.im ^ 2 by exact sq_abs z.im,
    inv_pow, div_eq_mul_inv]

private theorem phase_difference_bound {z : ℂ} (hz : z.re = 0) (u h : ℝ) :
    ‖Complex.exp (z * ((u+h : ℝ) : ℂ)) - Complex.exp (z * (u : ℂ))‖ ≤ |z.im| * |h| ∧
    ‖Complex.exp (z * ((u+h : ℝ) : ℂ)) - Complex.exp (z * (u : ℂ))‖ ≤ 2 := by
  have hnorm (v : ℝ) : ‖Complex.exp (z * (v : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re, hz]
  refine ⟨?_, (norm_sub_le _ _).trans (by rw [hnorm, hnorm]; norm_num)⟩
  have he : z = (z.im : ℂ) * Complex.I := by
    simpa only [hz, Complex.ofReal_zero, zero_add] using (Complex.re_add_im z).symm
  have hx : z * (h : ℂ) = Complex.I * ((z.im*h : ℝ) : ℂ) := by
    conv_lhs => rw [he]
    push_cast
    ring
  rw [Complex.ofReal_add, mul_add, Complex.exp_add,
    show Complex.exp (z * (u : ℂ)) * Complex.exp (z * (h : ℂ)) -
        Complex.exp (z * (u : ℂ)) =
      Complex.exp (z * (u : ℂ)) * (Complex.exp (z * (h : ℂ)) - 1) by ring,
    norm_mul, hnorm, one_mul, hx]
  simpa only [Real.norm_eq_abs, abs_mul] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := z.im*h))

private theorem centered_series_increment_le (hRH : RiemannHypothesis) {r : ℝ}
    (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ u h L : ℝ, 0 < L → L ≤ 1/4 → |h| ≤ L →
      let series (x : ℝ) := ∑' k, rootCoeff r k * Complex.exp (frequency k / (r : ℂ) * (x : ℂ))
      ‖series (u+h) - series u‖ ≤ C*L*(1+Real.log L⁻¹)^2 := by
  obtain ⟨A, hA, hlow⟩ := actual_low_weight
  obtain ⟨B, hB, hhigh⟩ := actual_high_weight
  have hr₀ : 0 < r := zero_lt_one.trans hr
  refine ⟨A+2*r*B+1, by positivity, fun u h L hL hL₁ hshift => ?_⟩
  let T := L⁻¹
  have hT : 2 ≤ T := by
    dsimp only [T]
    rw [inv_eq_one_div, le_div_iff₀ hL]
    linarith
  let low (k : ℕ) := if |(actualZero k).im| ≤ T then 1/‖actualZero k‖ else 0
  let high (k : ℕ) := if T < |(actualZero k).im| then ((actualZero k).im)⁻¹ ^ 2 else 0
  have hl : Summable low := (hlow T hT).1
  have hinv : Summable (fun k : ℕ => ((actualZero k).im)⁻¹ ^ 2) := by
    simpa only [Function.comp_def, actualZero] using
      actualOccurrenceEquiv.summable_iff.mpr actual_sigma_inverse_square_summable
  have hh : Summable high := Summable.of_nonneg_of_le
    (fun k => by unfold high; split_ifs <;> positivity)
    (fun k => by unfold high; split_ifs; exact le_rfl; positivity) hinv
  let term (x : ℝ) (k : ℕ) := rootCoeff r k * Complex.exp (frequency k / (r : ℂ) * (x : ℂ))
  have hre (k : ℕ) : (frequency k / (r : ℂ)).re = 0 := by
    simp [Complex.div_re, frequency_real hRH k]
  have hnorm (x : ℝ) (k : ℕ) : ‖term x k‖ = ‖rootCoeff r k‖ := by
    simp [term, Complex.norm_exp, Complex.mul_re, hre]
  have hterm (x : ℝ) : Summable (fun k => term x k) := by
    apply Summable.of_norm
    simpa only [hnorm] using Summable.of_nonneg_of_le (fun k => norm_nonneg (rootCoeff r k))
      (rootCoeff_bound hr) (actualCoeff_hasSum.summable.norm.mul_left r)
  have hpoint (k : ℕ) :
      ‖term (u+h) k - term u k‖ ≤ L * low k + 2*r * high k := by
    have hz : (frequency k / (r : ℂ)).im = (actualZero k).im / r := by
      simp [frequency, Complex.div_im, Complex.normSq_ofReal]
      field_simp [hr₀.ne']
    have hp := phase_difference_bound (hre k) u h
    obtain ⟨hc, hsq⟩ := root_coeff_frequency_bound hr₀ k
    change ‖rootCoeff r k * _ - rootCoeff r k * _‖ ≤ _
    rw [← mul_sub, norm_mul]
    by_cases hk : |(actualZero k).im| ≤ T
    · simp only [low, high, ite_eq_left hk, ite_eq_right (not_lt.mpr hk), mul_zero, add_zero]
      rw [hz, abs_div, abs_of_pos hr₀] at hp
      calc
        _ ≤ ‖rootCoeff r k‖ * (|(actualZero k).im| / r * |h|) :=
          mul_le_mul_of_nonneg_left hp.1 (norm_nonneg _)
        _ = (‖rootCoeff r k‖ * |(actualZero k).im|) / r * |h| := by ring
        _ ≤ (r / ‖actualZero k‖) / r * L := by
          exact mul_le_mul (div_le_div_of_nonneg_right hc hr₀.le) hshift
            (abs_nonneg _) (by positivity)
        _ = _ := by field_simp [hr₀.ne']
    · simp only [low, high, ite_eq_right hk, ite_eq_left (lt_of_not_ge hk), mul_zero, zero_add]
      calc
        _ ≤ ‖rootCoeff r k‖ * 2 := mul_le_mul_of_nonneg_left hp.2 (norm_nonneg _)
        _ ≤ _ := by nlinarith
  have hsum := tsum_of_norm_bounded
    ((hl.hasSum.mul_left L).add (hh.hasSum.mul_left (2*r))) hpoint
  rw [(hterm (u+h)).tsum_sub (hterm u)] at hsum
  have hLn : 1 ≤ 1 + Real.log T := by
    linarith [Real.log_nonneg (show 1 ≤ T by linarith)]
  have hTinv : T⁻¹ = L := inv_inv L
  have hlow' := mul_le_mul_of_nonneg_left (hlow T hT).2 hL.le
  have hhigh' := mul_le_mul_of_nonneg_left (hhigh T hT) (show 0 ≤ 2*r by positivity)
  have hreduce : 2*r * (B * (1 + Real.log T) / T) ≤
      2*r*B*L*(1+Real.log T)^2 := by
    rw [div_eq_mul_inv, hTinv]
    have hhlog : 1 + Real.log T ≤ (1 + Real.log T)^2 := by nlinarith
    calc
      _ = (2*r*B*L) * (1 + Real.log T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hhlog (by positivity)
  dsimp only
  exact hsum.trans ((add_le_add hlow' (hhigh'.trans hreduce)).trans
    (by dsimp only [T]; nlinarith [mul_nonneg hL.le (sq_nonneg (1+Real.log L⁻¹))]))

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
