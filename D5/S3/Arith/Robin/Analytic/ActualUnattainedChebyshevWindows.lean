/- GID: D5/S3/Arith/Robin/Analytic/ActualUnattainedChebyshevWindows
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/ActualUnattainedChebyshevWindows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual Chebyshev tail has both signs in every late fixed log window. -/

import D5.S3.Analytic.Asymptotics.PositiveAverageCosineWindow
import D5.S3.Arith.Robin.Analytic.ActualUnattainedAbscissaFilter
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualFilteredLeadingPair

/-! Local oscillation of the actual Chebyshev tail from an isolated zero pair. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped ComplexConjugate Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa)
open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualFilteredLeadingPair (actual_filtered_leading_pair)
open D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace D5.S3.Arith.Robin.Analytic.ActualUnattainedChebyshevWindows

theorem q_integrable_average {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {h t : ℝ} (hν : ν (Icc 0 h) = 1) (ht : Real.log 2 ≤ t) :
    Integrable (fun s => Q (Real.exp (t + s))) ν := by
  have hQ : ContinuousOn Q (Ici (1 : ℝ)) :=
    chebyshev_error_kernel_integrable.continuousOn_Ici_primitive_Ioi
  have hc : ContinuousOn (fun s => Q (Real.exp (t + s))) (Icc 0 h) :=
    hQ.comp (by fun_prop) (fun s hs => by
      apply mem_Ici.mpr
      have hts : 0 ≤ t + s := add_nonneg
        ((Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans ht) hs.1
      exact Real.one_le_exp hts)
  have hrestrict : ν.restrict (Icc 0 h) = ν := Measure.restrict_eq_self_of_ae_mem
    ((mem_ae_iff_prob_eq_one measurableSet_Icc).2 hν)
  have h := hc.integrableOn_Icc (μ := ν)
  rwa [IntegrableOn, hrestrict] at h

/-- When the actual zero abscissa is unattained, every late fixed logarithmic
window contains both signs of the complete Chebyshev tail. The excursion has
a fixed power exponent from a zero strictly to the right of the prescribed strip. -/
theorem eventually_actual_chebyshev_tail_two_signs {σ h : ℝ}
    (hσ : 1 / 2 < σ) (hσΘ : σ < zeroAbscissa) (hh : 0 < h)
    (hun : ∀ z : ℂ, D5.S3.Weil.ZeroSum.IsNontrivialZero z → z.re < zeroAbscissa) :
    ∃ β : ℝ, σ < β ∧ β < 1 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ T : ℝ in atTop,
        (∃ t ∈ Icc T (T + h), c * Real.exp ((β - 1) * T) < Q (Real.exp t)) ∧
        (∃ t ∈ Icc T (T + h), Q (Real.exp t) < -(c * Real.exp ((β - 1) * T))) := by
  let width := h / 2
  have hwidth : 0 < width := half_pos hh
  obtain ⟨p, b, ν, hγ, hfast, hb, hbρ, hνprob, hν, hkill, hmoment⟩ :=
    ActualUnattainedAbscissaFilter.exists_dominant_actual_zero_filter hσ hσΘ hwidth
      (F := 2 * Real.pi / width) hun
  let _ : IsProbabilityMeasure ν := hνprob
  let ρ := actualZero p
  let a := actualCoeff p * PositiveSpectralKernel.expMoment ν (ρ - 1)
  let C : ℝ := 2 * (analyticOrderNatAt riemannZeta ρ : ℝ) * ‖a‖
  let E : ℝ := (∑' k : ℕ, ‖actualCoeff k‖) + Real.log (2 * Real.pi)
  have hρ : ρ.re < 1 := (actualData.zero_isNontrivial (actualOccurrenceEquiv p).1).2.2
  have hb₀ : 0 ≤ b := by linarith only [hσ, hb]
  have hpair := actual_filtered_leading_pair ν p hν hb₀ hbρ hγ hmoment hkill
  change a ≠ 0 ∧ 0 < C ∧ b - 1 < ρ.re - 1 ∧ 0 ≤ E ∧
    ∃ R : ℝ → ℝ, ∀ t : ℝ, Real.log 2 ≤ t →
      (∫ s : ℝ, Q (Real.exp (t + s)) ∂ν) =
        -(C * Real.exp ((ρ.re - 1) * t) * Real.cos (ρ.im * t + a.arg)) + R t ∧
      |R t| ≤ E * Real.exp ((b - 1) * t) at hpair
  obtain ⟨_, hC, _, _, R, hR⟩ := hpair
  have hperiod : 2 * Real.pi / ρ.im ≤ width := by
    apply (div_le_iff₀ hγ).2
    have hf := (div_lt_iff₀ hwidth).1 hfast
    nlinarith only [hf]
  have hlimit : Tendsto (fun t : ℝ => E * Real.exp ((b - ρ.re) * t)) atTop (𝓝 0) := by
    have hdecay := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (sub_neg.mpr hbρ))
    simpa only [Function.comp_def, id_eq, mul_zero] using hdecay.const_mul E
  obtain ⟨T₀, hsmall⟩ := eventually_atTop.mp
    (hlimit.eventually_lt_const (half_pos hC))
  let c := C * Real.exp ((ρ.re - 1) * width) / 4
  refine ⟨ρ.re, hb.trans_lt hbρ, hρ, c, by dsimp [c]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.log 2), eventually_ge_atTop T₀] with T hT hT₀
  have hnegative : ρ.re - 1 ≤ 0 := sub_nonpos.mpr hρ.le
  have hA := PositiveAverageCosineWindow.exists_signed_values
    (f := fun t => Q (Real.exp t)) (scale := fun t => Real.exp ((ρ.re - 1) * t))
    (start := T) (width := width) (support := width) (phase := a.arg + Real.pi)
    (lower := Real.exp ((ρ.re - 1) * (T + width)))
    hγ hperiod hC (Real.exp_pos _)
    (fun t ht => Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.2 hnegative)) ?_
  · have hend : T + width + width = T + h := by dsimp [width]; ring
    have hlevel : C * Real.exp ((ρ.re - 1) * (T + width)) / 4 =
        c * Real.exp ((ρ.re - 1) * T) := by
      rw [mul_add, Real.exp_add]
      dsimp only [c]
      ring
    simpa only [hend, hlevel] using hA
  · intro t ht
    have hlog : Real.log 2 ≤ t := hT.trans ht.1
    obtain ⟨hidentity, hbound⟩ := hR t hlog
    refine ⟨ν, hνprob, hν, q_integrable_average hν hlog, ?_⟩
    have hphase : ρ.im * t + (a.arg + Real.pi) = (ρ.im * t + a.arg) + Real.pi :=
      (add_assoc _ _ _).symm
    rw [hidentity, hphase, Real.cos_add_pi, mul_neg, add_sub_cancel_left]
    refine hbound.trans ?_
    have hexp : Real.exp ((b - 1) * t) =
        Real.exp ((b - ρ.re) * t) * Real.exp ((ρ.re - 1) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp, ← mul_assoc]
    have hhsmall := hsmall t (hT₀.trans ht.1)
    exact (mul_le_mul_of_nonneg_right hhsmall.le (Real.exp_pos _).le).trans_eq (by ring)

end D5.S3.Arith.Robin.Analytic.ActualUnattainedChebyshevWindows
