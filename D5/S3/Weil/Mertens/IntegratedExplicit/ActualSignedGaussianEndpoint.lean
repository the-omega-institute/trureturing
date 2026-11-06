/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualSignedGaussianEndpoint
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualSignedGaussianEndpoint
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: The complete actual zeta formula supplies the signed logarithmic endpoint without JY. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.SignedGaussianEndpoint
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualZeroLaplace
import D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity
import D5.S3.Arith.Robin.OffLinePeak.ZeroCoefficientBudget

/-! The actual enumeration retains both ordinate signs and every analytic
multiplicity. The mass, height, explicit formula and trivial-zero correction
are existing suppliers. The new inference instantiates the signed endpoint.
All conclusions are analytic families, not finite numerical certificates. -/

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory MeasureTheory.Measure Filter
open scoped BigOperators Topology
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit.GaussianWindow
open D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent
open D5.S3.Weil.Mertens.IntegratedExplicit.SpectralAverage
open D5.S3.Weil.Mertens.IntegratedExplicit.SignedGaussianEndpoint
open D5.S3.Arith.Robin.CompleteMertensPeak
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Arith.Robin.OffLinePeak

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualSignedGaussianEndpoint

/-- The existing actual coefficient mass in the canonical positive-peak convention.
This consumed normalization is used by both the signed and positive endpoints. -/
theorem actual_coefficient_mass :
    HasSum (fun k : ℕ => (actualZero k * (1 - actualZero k))⁻¹)
      (ZeroCoefficientBudget.massConstant : ℂ) := by
  have hs : (2 * sqrt Real.pi) ^ 2 = 4 * Real.pi := by
    nlinarith [Real.sq_sqrt Real.pi_pos.le]
  have hm : firstLiMass = ZeroCoefficientBudget.massConstant := by
    unfold firstLiMass ZeroCoefficientBudget.massConstant
    rw [← hs, Real.log_pow]
  simpa only [actualCoeff, one_div, hm] using actualCoeff_hasSum

private def actualCompleteSpectrum : CountableSpectrum where
  zero := actualZero
  coeff := actualCoeff
  strip := fun k => (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2
  height := fun k => actual_height_gt_ten _
    (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)
  summable_norm := actualCoeff_hasSum.summable.norm
  mass_le := by
    obtain ⟨_, c, hc, _⟩ := actual_complete_H_package
    obtain ⟨_, _, _, _, hm, _, _, _⟩ := ZeroCoefficientBudget.zero_coefficient_budget
      actualZero (fun k => (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2)
      c hc (fun k => actual_height_gt_ten _
        (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)) actual_coefficient_mass
    simpa only [ZeroCoefficientBudget.coefficient, actualCoeff, one_div] using hm.le

private def actualCompleteCorrection : BoundedCorrection where
  value := trivialT
  measurable := (trivialT_continuousOn.mono Ioi_subset_Ici_self).aestronglyMeasurable
    measurableSet_Ioi
  nonneg := fun v hv => trivialT_nonneg hv.le
  le_one := by
    intro v hv
    have hb := trivialT_le_mass hv.le
    have hl : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
    linarith

private lemma Q_exp_neg_U {v : ℝ} (hv : log 2 ≤ v) :
    Q (exp v) = -U (exp v) / exp v := by
  have ht : 2 ≤ exp v := by
    calc
      (2 : ℝ) = exp (log 2) := (exp_log (by norm_num)).symm
      _ ≤ _ := exp_le_exp.mpr hv
  have h := D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
    D5.S3.Weil.Mertens.WeightedPrimeLimit.chebyshev_error_kernel_integrable ht
  change Q (exp v) = _ at h
  rw [h]
  dsimp [U]
  field_simp [(exp_pos v).ne']
  <;> ring

private lemma actual_complete_representation {v : ℝ} (hv : log 2 ≤ v) :
    Q (exp v) = signedQ actualCompleteSpectrum actualCompleteCorrection v := by
  have hv0 : 0 < v := (log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hv
  have hreal : (actualH v).re = U (exp v) - log (2 * Real.pi) + trivialT v := by
    have h := congrArg Complex.re (actual_integrated_explicit_formula hv0)
    simpa only [Complex.ofReal_re] using h
  have he : spectralSeries actualCompleteSpectrum v = actualH v * (exp (-v) : ℂ) := by
    have hterm (k : ℕ) : actualCoeff k * Complex.exp ((actualZero k - 1) * v) =
        (actualCoeff k * Complex.exp ((v : ℂ) * actualZero k)) * (exp (-v) : ℂ) := by
      rw [Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    simp only [spectralSeries, spectralExp, actualCompleteSpectrum, hterm,
      tsum_mul_right, actualH]
  rw [Q_exp_neg_U hv]
  dsimp only [signedQ, actualCompleteCorrection]
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hreal, div_eq_mul_inv, ← exp_neg]
  ring

/-- Full actual signed endpoint, with integrability and its proved mean bound. -/
theorem actual_complete_signed_gaussian_endpoint {H A : ℝ}
    (hH : 20000 ≤ H) (hA : 10000 ≤ A) (hAH : A ≤ exp H) :
    (IntegrableOn (fun y : ℝ => ∫ v : ℝ in Ioi y, W v * Q (exp v))
      (Icc H (4 * (H + 20) ^ 2)) (gaussian (H + 20))) ∧
    (|∫ y : ℝ in Icc H (4 * (H + 20) ^ 2),
      (∫ v : ℝ in Ioi y, W v * Q (exp v)) ∂gaussian (H + 20)| ≤
        1000 * exp (-H) / H) ∧
    (∃ y ∈ Icc H (4 * (H + 20) ^ 2), -(1 / (2 * sqrt A)) <
      (∫ v : ℝ in Ioi y, W v * Q (exp v)) / R y) := by
  have hlog : log (2 : ℝ) ≤ H := by
    have hb := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hq : ∀ v : ℝ, H ≤ v → Q (exp v) =
      signedQ actualCompleteSpectrum actualCompleteCorrection v :=
    fun v hv => actual_complete_representation (hlog.trans hv)
  have he : (fun y : ℝ => ∫ v : ℝ in Ioi y, W v * Q (exp v)) =ᵐ[windowMeasure H]
      signedG actualCompleteSpectrum actualCompleteCorrection := by
    change ∀ᵐ y : ℝ ∂(gaussian (H + 20)).restrict (window H), _
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [hq v (hy.1.trans hv.le)]
  refine ⟨(signedG_window_integrable actualCompleteSpectrum actualCompleteCorrection
    (by linarith)).congr he.symm, ?_, ?_⟩
  · change |∫ y : ℝ, (∫ v : ℝ in Ioi y, W v * Q (exp v)) ∂windowMeasure H| ≤ _
    rw [integral_congr_ae he]
    exact full_summed_average_bound actualCompleteSpectrum actualCompleteCorrection hH
  · exact endpoint_of_complete_representation actualCompleteSpectrum actualCompleteCorrection
      hH hA hAH hq

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualSignedGaussianEndpoint
