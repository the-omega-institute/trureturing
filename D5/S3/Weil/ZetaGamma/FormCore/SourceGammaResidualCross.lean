/- GID: D5/S3/Weil/ZetaGamma/FormCore/SourceGammaResidualCross
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:actual-gamma-residual-cross-series)
   anchors: []
   utility: none
   digest: Actual residual cross series with the complete signed resonance row. -/

/- SOURCE_ONLY / UNCOMPILED, 2026-10-25.
Actual L1 residual multiplier cross series. Adapted to the verified final
five-conjunct residual L1 supplier and the current six-supplier actual kernel
owner; the spectral owner still supplies the literal bare weight notation.
No native verification, Reg packaging, KPI or admission claim is made. -/

import D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.SourceGammaResidualCross

open MeasureTheory Set Filter
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal
open D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure
open scoped Topology ComplexConjugate FourierTransform ENNReal

private abbrev halfline : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
private def zeroExtension (u : ℝ → ℂ) : ℝ → ℂ := (Ioi (0 : ℝ)).indicator u

def actualSourceSpectralCross (u : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
    unitarySourceFourier (zeroExtension u) (-ξ)

private def actualSourceFourierBound (u : ℝ → ℂ) : ℝ :=
  ‖((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)⁻¹‖ * ∫ t : ℝ, ‖zeroExtension u t‖

private theorem actualSourceFourierBound_nonneg (u : ℝ → ℂ) :
    0 ≤ actualSourceFourierBound u :=
  mul_nonneg (norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)

private theorem actual_unitary_fourier_norm_le (u : ℝ → ℂ) (ξ : ℝ) :
    ‖unitarySourceFourier (zeroExtension u) ξ‖ ≤ actualSourceFourierBound u := by
  rw [unitarySourceFourier_eq_integral, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ∫ t : ℝ, ‖sourcePhase ξ t * zeroExtension u t‖ := norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_mul, sourcePhase_norm, one_mul]

private theorem actual_source_cross_norm_le (u : ℝ → ℂ) (ξ : ℝ) :
    ‖actualSourceSpectralCross u ξ‖ ≤ actualSourceFourierBound u ^ 2 := by
  simp only [actualSourceSpectralCross, norm_mul, Complex.norm_conj]
  simpa only [pow_two] using mul_le_mul
    (actual_unitary_fourier_norm_le u ξ) (actual_unitary_fourier_norm_le u (-ξ))
    (norm_nonneg _) (actualSourceFourierBound_nonneg u)

private theorem actual_source_cross_measurable {u : ℝ → ℂ}
    (hu : Integrable u halfline) : AEStronglyMeasurable (actualSourceSpectralCross u) volume := by
  have hU : Integrable (zeroExtension u) volume :=
    (integrable_indicator_iff measurableSet_Ioi).2 hu
  have hF : Continuous (unitarySourceFourier (zeroExtension u)) := by
    unfold unitarySourceFourier
    exact continuous_const.mul
      ((D5.S3.Weil.ZetaGamma.FormCore.LineFourier.continuous_raw_fourier hU).comp
        (by fun_prop))
  exact ((Complex.continuous_conj.comp hF).mul (hF.comp continuous_neg)).aestronglyMeasurable

/-- The literal Fourier cross is an actual bounded functional on real L1
multipliers. This pays both domain and the norm used for series exchange. -/
private theorem actual_l1_real_multiplier_cross_domain_and_norm
    {p : ℝ → ℝ} (hp : Integrable p volume) {u : ℝ → ℂ}
    (hu : Integrable u halfline) :
    Integrable (fun ξ : ℝ => (p ξ : ℂ) * actualSourceSpectralCross u ξ) volume ∧
    (∫ ξ : ℝ, ‖(p ξ : ℂ) * actualSourceSpectralCross u ξ‖) ≤
      actualSourceFourierBound u ^ 2 * ∫ ξ : ℝ, ‖p ξ‖ := by
  have hmeas := (Complex.continuous_ofReal.comp_aestronglyMeasurable
    hp.aestronglyMeasurable).mul (actual_source_cross_measurable hu)
  have hPoint (ξ : ℝ) :
      ‖(p ξ : ℂ) * actualSourceSpectralCross u ξ‖ ≤
        actualSourceFourierBound u ^ 2 * ‖p ξ‖ := by
    simp only [norm_mul, Complex.norm_real]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (actual_source_cross_norm_le u ξ) (norm_nonneg (p ξ))
  have hI := (hp.norm.const_mul (actualSourceFourierBound u ^ 2)).mono'
    hmeas (Eventually.of_forall hPoint)
  refine ⟨hI, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hI.norm (hp.norm.const_mul _) hPoint

def actualResidualLayer (a c ξ : ℝ) : ℝ :=
  ξ ^ 2 / (c * (ξ ^ 2 + c ^ 2) * (ξ ^ 2 + a ^ 2))

def literalSourceLaplace (a : ℝ) (u : ℝ → ℂ) : ℂ :=
  ∫ t : ℝ, (Real.exp (-a * t) : ℂ) * u t ∂halfline

def literalSourceFirstLaplaceMoment (a : ℝ) (u : ℝ → ℂ) : ℂ :=
  ∫ t : ℝ, (t : ℂ) * (Real.exp (-a * t) : ℂ) * u t ∂halfline

def actualResidualLayerCrossValue (a c : ℝ) (u : ℝ → ℂ) : ℝ :=
  if c = a then
    Complex.normSq (literalSourceLaplace a u) / (4 * a ^ 2) -
      ((starRingEnd ℂ) (literalSourceLaplace a u) *
        literalSourceFirstLaplaceMoment a u).re / (2 * a)
  else
    Complex.normSq (literalSourceLaplace c u) / (2 * (c ^ 2 - a ^ 2)) -
      a * Complex.normSq (literalSourceLaplace a u) /
        (2 * c * (c ^ 2 - a ^ 2))

private theorem actual_residual_layer_partial_fraction
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hca : c ≠ a) (ξ : ℝ) :
    (actualResidualLayer a c ξ : ℂ) =
      ((c / (c ^ 2 - a ^ 2) : ℝ) : ℂ) * actualResolventSymbol c ξ -
        ((a ^ 2 / (c * (c ^ 2 - a ^ 2)) : ℝ) : ℂ) * actualResolventSymbol a ξ := by
  have hd : c ^ 2 - a ^ 2 ≠ 0 := by
    intro h
    have hs : c ^ 2 = a ^ 2 := sub_eq_zero.mp h
    exact hca ((sq_eq_sq₀ hc.le ha.le).mp hs)
  have hdc : ξ ^ 2 + c ^ 2 ≠ 0 := by positivity
  have hda : ξ ^ 2 + a ^ 2 ≠ 0 := by positivity
  unfold actualResidualLayer actualResolventSymbol
  norm_cast
  field_simp [hc.ne', hd, hdc, hda]
  <;> ring

/-- Nonresonant and resonant layers both consume actual inverse kernels;
the mixed first moment survives exactly at c=a. No kernel identity is a premise. -/
theorem actual_residual_layer_cross_value
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) {u : ℝ → ℂ}
    (hu : Integrable u halfline) :
    (∫ ξ : ℝ, (actualResidualLayer a c ξ : ℂ) * actualSourceSpectralCross u ξ).re =
      actualResidualLayerCrossValue a c u := by
  by_cases hca : c = a
  · subst c
    rw [actualResidualLayerCrossValue, if_pos rfl]
    have hPoint (ξ : ℝ) :
        (actualResidualLayer a a ξ : ℂ) = actualResonantSymbol a ξ := by
      unfold actualResidualLayer actualResonantSymbol
      congr 1
      ring
    simp_rw [hPoint]
    convert (actual_resonant_reflected_cross_laplace_moment ha hu).2 using 1
    · apply congrArg Complex.re
      apply integral_congr_ae
      exact Eventually.of_forall fun ξ => (mul_assoc _ _ _).symm
    · rfl
  · simp only [actualResidualLayerCrossValue, if_neg hca]
    obtain ⟨_, hA₀, hAi₀⟩ := actual_resolvent_reflected_cross_laplace_square ha hu
    obtain ⟨_, hC₀, hCi₀⟩ := actual_resolvent_reflected_cross_laplace_square hc hu
    have hA : Integrable (fun ξ => actualResolventSymbol a ξ * actualSourceSpectralCross u ξ) volume := by
      convert hA₀ using 1
      funext ξ
      exact (mul_assoc _ _ _).symm
    have hC : Integrable (fun ξ => actualResolventSymbol c ξ * actualSourceSpectralCross u ξ) volume := by
      convert hC₀ using 1
      funext ξ
      exact (mul_assoc _ _ _).symm
    have hAi : (∫ ξ, actualResolventSymbol a ξ * actualSourceSpectralCross u ξ) =
        (Complex.normSq (literalSourceLaplace a u) : ℂ) / ((2 * a : ℝ) : ℂ) := by
      convert hAi₀ using 1
      congr 1
      funext ξ
      exact (mul_assoc _ _ _).symm
      all_goals rfl
    have hCi : (∫ ξ, actualResolventSymbol c ξ * actualSourceSpectralCross u ξ) =
        (Complex.normSq (literalSourceLaplace c u) : ℂ) / ((2 * c : ℝ) : ℂ) := by
      convert hCi₀ using 1
      congr 1
      funext ξ
      exact (mul_assoc _ _ _).symm
      all_goals rfl
    have hInt : (∫ ξ, (actualResidualLayer a c ξ : ℂ) * actualSourceSpectralCross u ξ) =
        ((c / (c ^ 2 - a ^ 2) : ℝ) : ℂ) *
          (Complex.normSq (literalSourceLaplace c u) : ℂ) / ((2 * c : ℝ) : ℂ) -
        ((a ^ 2 / (c * (c ^ 2 - a ^ 2)) : ℝ) : ℂ) *
          (Complex.normSq (literalSourceLaplace a u) : ℂ) / ((2 * a : ℝ) : ℂ) := by
      simp_rw [actual_residual_layer_partial_fraction ha hc hca, sub_mul, mul_assoc]
      rw [integral_sub (hC.const_mul _) (hA.const_mul _),
        integral_const_mul, integral_const_mul, hAi, hCi]
      ring
    rw [hInt]
    simp only [Complex.sub_re, Complex.div_ofReal_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    have hd : c ^ 2 - a ^ 2 ≠ 0 := by
      intro h
      exact hca ((sq_eq_sq₀ hc.le ha.le).mp (sub_eq_zero.mp h))
    field_simp [ha.ne', hc.ne', hd]
    <;> ring

/-- The actual L1 residual cross is the complete absolutely integrable
layer series, with the resonant mixed term retained. Only original source
L1 is needed; no Gamma/quarter graph or target identity is assumed. -/
theorem actual_residual_reflected_cross_complete_series
    {a : ℝ} (ha : 0 < a) {u : ℝ → ℂ} (hu : Integrable u halfline) :
    Integrable (fun ξ : ℝ =>
      ((actualBareQuarterWeight ξ / (ξ ^ 2 + a ^ 2) : ℝ) : ℂ) *
        actualSourceSpectralCross u ξ) volume ∧
    HasSum (fun n : ℕ => actualResidualLayerCrossValue a ((n : ℝ) + 1 / 4) u)
      (∫ ξ : ℝ,
        ((actualBareQuarterWeight ξ / (ξ ^ 2 + a ^ 2) : ℝ) : ℂ) *
          actualSourceSpectralCross u ξ).re := by
  obtain ⟨hQ, hNorms, hLayers, _, hBare⟩ :=
    D5.S3.Weil.ZetaGamma.FormCore.ActualGammaResidualL1.actual_digamma_quarter_resolvent_l1_domain_and_series
      a ha
  have hQi : Integrable (fun ξ : ℝ =>
      actualBareQuarterWeight ξ / (ξ ^ 2 + a ^ 2)) volume := by
    simpa only [actualBareQuarterWeight] using hQ
  let P : ℕ → ℝ → ℝ := fun n => actualResidualLayer a ((n : ℝ) + 1 / 4)
  let R : ℕ → ℝ → ℂ := fun n ξ => (P n ξ : ℂ) * actualSourceSpectralCross u ξ
  have hPi (n : ℕ) : Integrable (P n) volume := (hLayers n).1
  have hPn (n : ℕ) : (∫ ξ : ℝ, ‖P n ξ‖) =
      Real.pi / (((n : ℝ) + 1 / 4) * (a + ((n : ℝ) + 1 / 4))) := (hLayers n).2
  have hRi (n : ℕ) : Integrable (R n) volume :=
    (actual_l1_real_multiplier_cross_domain_and_norm (hPi n) hu).1
  have hRnorms : Summable (fun n : ℕ => ∫ ξ : ℝ, ‖R n ξ‖) := by
    apply Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun ξ => norm_nonneg (R n ξ))
      (fun n => ?_) (Summable.mul_left (actualSourceFourierBound u ^ 2) hNorms)
    have h : (∫ ξ : ℝ, ‖R n ξ‖) ≤
        actualSourceFourierBound u ^ 2 * ∫ ξ : ℝ, ‖P n ξ‖ :=
      (actual_l1_real_multiplier_cross_domain_and_norm (hPi n) hu).2
    rw [hPn n] at h
    exact h
  have hPoint (ξ : ℝ) : HasSum (fun n : ℕ => P n ξ)
      (actualBareQuarterWeight ξ / (ξ ^ 2 + a ^ 2)) := by
    have hRows : (fun n : ℕ => P n ξ) = fun n : ℕ =>
        (1 / ((n : ℝ) + 1 / 4) -
          ((n : ℝ) + 1 / 4) / (ξ ^ 2 + ((n : ℝ) + 1 / 4) ^ 2)) /
            (ξ ^ 2 + a ^ 2) := by
      funext n
      have hc : (n : ℝ) + 1 / 4 ≠ 0 := by positivity
      have hdc : ξ ^ 2 + ((n : ℝ) + 1 / 4) ^ 2 ≠ 0 := by positivity
      have hda : ξ ^ 2 + a ^ 2 ≠ 0 := by positivity
      dsimp [P, actualResidualLayer]
      field_simp [hc, hdc, hda]
      <;> ring
    rw [hRows]
    simpa only [actualBareQuarterWeight] using
      (hBare ξ).div_const (ξ ^ 2 + a ^ 2)
  have hCrossPoint (ξ : ℝ) : HasSum (fun n : ℕ => R n ξ)
      (((actualBareQuarterWeight ξ / (ξ ^ 2 + a ^ 2) : ℝ) : ℂ) *
        actualSourceSpectralCross u ξ) := by
    exact (Complex.hasSum_ofReal.mpr (hPoint ξ)).mul_right _
  have hS := hasSum_integral_of_summable_integral_norm hRi hRnorms
  have hCrossEq : (fun ξ : ℝ => ∑' n : ℕ, R n ξ) =
      fun ξ => ((actualBareQuarterWeight ξ / (ξ ^ 2 + a ^ 2) : ℝ) : ℂ) *
        actualSourceSpectralCross u ξ := funext fun ξ => (hCrossPoint ξ).tsum_eq
  rw [hCrossEq] at hS
  have hSR := Complex.reCLM.hasSum hS
  have hTerms (n : ℕ) : (∫ ξ, R n ξ).re =
      actualResidualLayerCrossValue a ((n : ℝ) + 1 / 4) u :=
    actual_residual_layer_cross_value ha (by positivity) hu
  refine ⟨(actual_l1_real_multiplier_cross_domain_and_norm hQi hu).1, ?_⟩
  simpa only [Complex.reCLM_apply, hTerms] using hSR

end D5.S3.Weil.ZetaGamma.FormCore.SourceGammaResidualCross
