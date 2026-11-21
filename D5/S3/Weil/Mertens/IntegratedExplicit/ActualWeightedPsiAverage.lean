/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualWeightedPsiAverage
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualWeightedPsiAverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The positive correction transfers an actual mode to the weighted psi tail. -/

import D5.S3.Analytic.Asymptotics.WeightedFilterStability
import D5.S3.Analytic.Asymptotics.WeightedFilterTailTransmutation
import D5.S3.Weil.Mertens.ActualPsiTailEulerBridge

/-! The weighted and unweighted psi tails use the same logarithmic source. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open D5.S3.Arith.Robin.CompleteMertensPeak (Q psiErrorKernel)
open D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (Jpsi)
open D5.S3.Weil.Mertens.PsiLaplaceContinuation (qpsi qpsi_measurable qpsi_integrable)
open D5.S3.Weil.Mertens.PsiLaplaceForcing (fpsi fpsi_eq_tail kpsi)
open WeightedFilterCDF (weight)
open WeightedFilterTailTransmutation (tailPrimitive)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualWeightedPsiAverage

private lemma unweighted_eq (t : ℝ) : tailPrimitive qpsi t = Q (Real.exp t) := by
  rw [tailPrimitive, integral_Ici_eq_integral_Ioi, Q, ← integral_comp_exp_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  dsimp only [psiErrorKernel, qpsi, smul_eq_mul]
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero]

private lemma weighted_eq (t : ℝ) :
    (∫ v in Ici t, weight v * qpsi v) = Jpsi (Real.exp t) := by
  have h := congrArg Neg.neg (fpsi_eq_tail t)
  simp only [fpsi, neg_neg] at h
  rw [integral_Ici_eq_integral_Ioi, h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  unfold weight kpsi
  ring

private lemma measurable_primitive : Measurable (tailPrimitive qpsi) := by
  let region : Set (ℝ × ℝ) := {p | p.1 ≤ p.2}
  have hregion : MeasurableSet region := measurableSet_le measurable_fst measurable_snd
  have hf : Measurable (region.indicator (fun p => qpsi p.2)) :=
    (qpsi_measurable.comp measurable_snd).indicator hregion
  have hint := (hf.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  convert hint using 1
  funext t
  unfold tailPrimitive
  have hpoint : (fun v : ℝ => region.indicator (fun p => qpsi p.2) (t, v)) =
      (Ici t).indicator qpsi := by
    funext v
    by_cases hv : t ≤ v <;> simp [region, hv]
  rw [hpoint, integral_indicator measurableSet_Ici]

/-- A compact correction of the probability average preserves the leading mode of
the actual psi tail, with the Robin weight and controlled errors for both exponents. -/
theorem exists_corrected_actual_psi_average
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {h t δ E : ℝ} {A lam : ℂ}
    (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 h) (ht : Real.log 2 ≤ t)
    (hlam : lam.re < 0) (hδ : δ < 0) (hE : 0 ≤ E)
    (happrox : ∀ v : ℝ, 0 ≤ v →
      |(∫ u, Q (Real.exp (t + v + u)) ∂μ) -
        (A * Complex.exp (lam * (v : ℂ))).re| ≤ E * Real.exp (δ * v)) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν (Icc 0 h)ᶜ = 0 ∧
      |(∫ u, Jpsi (Real.exp (t + u)) ∂ν) - (A * (weight t : ℂ)).re| ≤
        2 * E * weight t + ‖A‖ * (2 * (h + 1 / (-lam.re)) * (weight t / t)) := by
  have htpos : 0 < t := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le ht
  obtain ⟨ν, hprob, hsupport, havg⟩ :=
    WeightedFilterTailTransmutation.exists_compact_probability_weighted_tail_average_eq_laplace
      hμ htpos
  have hr : IntegrableOn qpsi (Ici t) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact qpsi_integrable.mono_set (Ioi_subset_Ioi ht)
  let B : ℝ → ℝ := fun v => ∫ u, tailPrimitive qpsi (t + v + u) ∂μ
  have hB : Measurable B := by
    have hfun : Measurable (fun p : ℝ × ℝ => tailPrimitive qpsi (t + p.1 + p.2)) :=
      measurable_primitive.comp (by fun_prop)
    exact (hfun.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have hBapprox (v : ℝ) (hv : 0 ≤ v) :
      |B v - (A * Complex.exp (lam * (v : ℂ))).re| ≤ E * Real.exp (δ * v) := by
    simpa only [B, unweighted_eq] using happrox v hv
  have hstable := WeightedFilterStability.abs_laplace_sub_re_response_le
    hμ htpos hlam hδ hE hB.aemeasurable hBapprox
  have heq := havg qpsi qpsi_measurable hr
  simp only [weighted_eq] at heq
  have heq' :
      (∫ u, Jpsi (Real.exp (t + u)) ∂ν) =
        ∫ y in Ici (0 : ℝ), ((1 + y) * Real.exp (-t * y) / WeightedFilterCDF.moment μ y) *
          (B 0 - y * (∫ v in Ici (0 : ℝ), Real.exp (-y * v) * B v)) := by
    simpa only [B, add_zero] using heq
  have hresponse := WeightedFilterLeadingMode.norm_response_sub_weight_le hμ htpos hlam
  have hmode :
      |(A * WeightedFilterLeadingMode.response μ lam t).re - (A * (weight t : ℂ)).re| ≤
        ‖A‖ * (2 * (h + 1 / (-lam.re)) * (weight t / t)) := by
    rw [← Complex.sub_re, ← mul_sub]
    exact (Complex.abs_re_le_norm _).trans
      (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left hresponse (norm_nonneg _))
  refine ⟨ν, hprob, hsupport, ?_⟩
  rw [heq']
  exact (abs_sub_le _ (A * WeightedFilterLeadingMode.response μ lam t).re _).trans
    (add_le_add hstable hmode)

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualWeightedPsiAverage
