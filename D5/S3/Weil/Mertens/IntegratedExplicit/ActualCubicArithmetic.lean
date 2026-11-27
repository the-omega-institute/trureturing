/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualCubicArithmetic
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualCubicArithmetic
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: The actual cubic spectral tail controls the normalized weighted Chebyshev error. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicEndpoint
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualSignedGaussianEndpoint
import D5.S3.Weil.Mertens.WeightedTailTransport

/-! The actual cubic spectral estimate gives a lower bound after logarithmic
transport of the weighted Chebyshev tail. The elementary term integrates exactly. -/

set_option autoImplicit false

noncomputable section

open Real Set MeasureTheory MeasureTheory.Measure Filter
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q psiErrorKernel)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (actualZero)
open D5.S3.Weil.Mertens.WeightedTailTransport (r weightedTail transport_exp)
open D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent
open D5.S3.Weil.Mertens.IntegratedExplicit.SignedGaussianEndpoint (signedQ)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualSignedGaussianEndpoint
  (actualCompleteSpectrum actualCompleteCorrection actual_complete_representation)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicEndpoint
  (cubicLowMass quadraticHighMass actual_spectral_tail_bound)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicArithmetic

private lemma W_exp_neg_tail {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun v : ℝ => W v * exp (-v)) (Ioi b) ∧
      (∫ v in Ioi b, W v * exp (-v)) = exp (-b) / b ^ 2 := by
  have hint : IntegrableOn (fun v : ℝ => W v * exp (-v)) (Ioi b) := by
    apply (W_tail_integrable hb).mul_bdd (c := 1)
      (show Continuous (fun v : ℝ => exp (-v)) by fun_prop).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.mpr (neg_nonpos.mpr (hb.trans hv).le)
  have hderiv (v : ℝ) (hv : v ∈ Ici b) :
      HasDerivAt (fun x : ℝ => -(exp (-x) / x ^ 2)) (W v * exp (-v)) v := by
    have hv0 : 0 < v := hb.trans_le hv
    have hd := ((hasDerivAt_id v).neg.exp.div
      ((hasDerivAt_id v).pow 2) (pow_ne_zero 2 hv0.ne')).neg
    change HasDerivAt (fun x : ℝ => -(exp (-x) / x ^ 2))
      (-((exp (-v) * -1 * v ^ 2 - exp (-v) * ((2 : ℝ) * v ^ (2 - 1 : ℕ) * 1)) /
        (v ^ 2) ^ 2)) v at hd
    convert hd using 1
    simp only [W, Nat.reduceSub, pow_one]
    field_simp [hv0.ne']
    ring
  have hinv : Tendsto (fun v : ℝ => v⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hlim : Tendsto (fun v : ℝ => exp (-v) / v ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 2 ≠ 0), mul_zero] using
      tendsto_exp_neg_atTop_nhds_zero.mul (hinv.pow 2)
  refine ⟨hint, ?_⟩
  simpa only [neg_zero, zero_sub, neg_neg] using
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim.neg

/-- A cutoff with exact critical-line real parts below it bounds the normalized
weighted Chebyshev tail from below. The elementary constant term is exact. -/
theorem actual_cubic_arithmetic_lower_bound {b T : ℝ} (hb : log 2 ≤ b) (hT : 0 < T)
    (hline : ∀ k : ℕ, |(actualZero k).im| ≤ T → (actualZero k).re = 1 / 2) :
    -(W b / R b) * (exp (-b / 2) * cubicLowMass T + quadraticHighMass T / T) -
        log (2 * Real.pi) * exp (-b) / (b + 1) ≤
      Q (exp b) - weightedTail psiErrorKernel (exp b) / r (exp b) := by
  have hb0 : 0 < b := (log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hb
  have hK : IntegrableOn psiErrorKernel (Ioi (exp b)) :=
    D5.S3.Weil.Mertens.WeightedPrimeLimit.chebyshev_error_kernel_integrable.mono_set
      (Ioi_subset_Ioi (le_of_lt (one_lt_exp_iff.mpr hb0)))
  obtain ⟨hint, htransport⟩ := transport_exp hb hK
  change IntegrableOn (fun v => W v * Q (exp v)) (Ioi b) at hint
  change R b * (Q (exp b) - weightedTail psiErrorKernel (exp b) / r (exp b)) =
    ∫ v in Ioi b, W v * Q (exp v) at htransport
  let F : ℝ → ℂ := fun v => (W v : ℂ) * spectralSeries actualCompleteSpectrum v
  let c : ℝ := log (2 * Real.pi)
  have hF : IntegrableOn F (Ioi b) := spectral_weighted_integrable _ hb0
  have hFneg : IntegrableOn (fun v => -(F v).re) (Ioi b) := hF.re.neg
  obtain ⟨helem, helem_eq⟩ := W_exp_neg_tail hb0
  have hpoint (v : ℝ) (hv : v ∈ Ioi b) :
      -(F v).re - c * (W v * exp (-v)) ≤ W v * Q (exp v) := by
    rw [actual_complete_representation (hb.trans hv.le)]
    simp only [F, signedQ, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    have hv0 : 0 < v := hb0.trans hv
    have htriv : 0 ≤ W v * (actualCompleteCorrection.value v * exp (-v)) :=
      mul_nonneg (W_nonneg hv0.le)
        (mul_nonneg (actualCompleteCorrection.nonneg v hv0) (exp_nonneg _))
    calc
      _ ≤ -(W v * (spectralSeries actualCompleteSpectrum v).re) -
          c * (W v * exp (-v)) + W v * (actualCompleteCorrection.value v * exp (-v)) :=
        le_add_of_nonneg_right htriv
      _ = _ := by dsimp only [c]; ring
  have htail := setIntegral_mono_on (hFneg.sub (helem.const_mul c)) hint measurableSet_Ioi hpoint
  change (∫ v in Ioi b, -(F v).re - c * (W v * exp (-v))) ≤ _ at htail
  have hre : (∫ v in Ioi b, (F v).re) = (spectralTail actualCompleteSpectrum b).re := by
    simpa only [RCLike.re_eq_complex_re, spectralTail, F] using integral_re hF
  rw [integral_sub hFneg (helem.const_mul c), integral_neg, hre, integral_const_mul,
    helem_eq, ← htransport] at htail
  let M : ℝ := exp (-b / 2) * cubicLowMass T + quadraticHighMass T / T
  have hnorm : ‖spectralTail actualCompleteSpectrum b‖ ≤ W b * M := by
    exact (actual_spectral_tail_bound hb0 hT hline).2.1
  have hR : 0 < R b := by unfold R; positivity
  change -(W b / R b) * M - c * exp (-b) / (b + 1) ≤ _
  apply (mul_le_mul_iff_right₀ hR).mp
  calc
    _ = -(W b * M) - c * (exp (-b) / b ^ 2) := by
      unfold R
      field_simp [hb0.ne', show b + 1 ≠ 0 by positivity]
    _ ≤ -(spectralTail actualCompleteSpectrum b).re - c * (exp (-b) / b ^ 2) :=
      sub_le_sub_right (neg_le_neg ((Complex.re_le_norm _).trans hnorm)) _
    _ ≤ R b * (Q (exp b) - weightedTail psiErrorKernel (exp b) / r (exp b)) := htail

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicArithmetic
