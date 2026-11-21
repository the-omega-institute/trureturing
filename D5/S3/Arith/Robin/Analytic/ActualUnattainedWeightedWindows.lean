/- GID: D5/S3/Arith/Robin/Analytic/ActualUnattainedWeightedWindows
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/ActualUnattainedWeightedWindows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Robin weighted tails oscillate in every late fixed logarithmic window. -/

import D5.S3.Analytic.Asymptotics.PositiveAverageCosineWindow
import D5.S3.Arith.Robin.Analytic.ActualUnattainedAbscissaFilter
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualFilteredLeadingPair
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualWeightedPsiAverage

/-! Short probability averages of the weighted tail preserve the isolated zero pair. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped ComplexConjugate Topology
open WeightedFilterCDF (weight)
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa)
open D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (Jpsi tails)
open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualFilteredLeadingPair (actual_filtered_leading_pair)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualWeightedPsiAverage
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace D5.S3.Arith.Robin.Analytic.ActualUnattainedWeightedWindows

private theorem jpsi_integrable_average {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {h t : ℝ} (hν : ∀ᵐ u ∂ν, u ∈ Icc 0 h) (ht : Real.log 2 ≤ t) :
    Integrable (fun u => Jpsi (Real.exp (t + u))) ν := by
  have hJ : ContinuousOn Jpsi (Ici (2 : ℝ)) :=
    (tails (x := 2) le_rfl).1.continuousOn_Ici_primitive_Ioi
  have hc : ContinuousOn (fun u => Jpsi (Real.exp (t + u))) (Icc 0 h) :=
    hJ.comp (by fun_prop) (fun u hu => by
      apply mem_Ici.mpr
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_le_exp.mpr (by linarith [hu.1]))
  have h := hc.integrableOn_Icc (μ := ν)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hν] at h

private theorem re_mode (ρ : ℂ) (C phase t : ℝ) :
    (((C : ℂ) * Complex.exp (Complex.I * (phase : ℂ))) *
      Complex.exp ((ρ - 1) * (t : ℂ))).re =
      C * Real.exp ((ρ.re - 1) * t) * Real.cos (ρ.im * t + phase) := by
  let z := Complex.I * (phase : ℂ) + (ρ - 1) * (t : ℂ)
  have hre : z.re = (ρ.re - 1) * t := by
    simp [z, Complex.mul_re]
  have him : z.im = ρ.im * t + phase := by
    simp [z, Complex.mul_im, add_comm]
  rw [mul_assoc, ← Complex.exp_add]
  change ((C : ℂ) * Complex.exp z).re = _
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_re, hre, him]
  ring

private theorem norm_mode (ρ : ℂ) {C : ℝ} (hC : 0 < C) (phase t : ℝ) :
    ‖((C : ℂ) * Complex.exp (Complex.I * (phase : ℂ))) *
      Complex.exp ((ρ - 1) * (t : ℂ))‖ = C * Real.exp ((ρ.re - 1) * t) := by
  simp [Complex.norm_exp, Complex.mul_re, abs_of_pos hC]

/-- Under unattainment the actual activation-weighted psi tail has both signs,
with a power lower bound divided by the logarithmic variable. -/
theorem eventually_actual_weighted_psi_tail_two_signs {σ h : ℝ}
    (hσ : 1 / 2 < σ) (hσΘ : σ < zeroAbscissa) (hh : 0 < h)
    (hun : ∀ z : ℂ, D5.S3.Weil.ZeroSum.IsNontrivialZero z → z.re < zeroAbscissa) :
    ∃ β : ℝ, σ < β ∧ β < 1 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ T : ℝ in atTop,
        (∃ t ∈ Icc T (T + h), c * Real.exp ((β - 1) * T) / T < Jpsi (Real.exp t)) ∧
        (∃ t ∈ Icc T (T + h), Jpsi (Real.exp t) < -(c * Real.exp ((β - 1) * T) / T)) := by
  let width := h / 2
  have hwidth : 0 < width := half_pos hh
  obtain ⟨p, b, μ, hγ, hfast, hb, hbρ, hμprob, hmass, hkill, hmoment⟩ :=
    ActualUnattainedAbscissaFilter.exists_dominant_actual_zero_filter hσ hσΘ hwidth
      (F := 2 * Real.pi / width) hun
  let _ : IsProbabilityMeasure μ := hμprob
  have hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 width :=
    (mem_ae_iff_prob_eq_one measurableSet_Icc).2 hmass
  let ρ := actualZero p
  let a := actualCoeff p * PositiveSpectralKernel.expMoment μ (ρ - 1)
  let C : ℝ := 2 * (analyticOrderNatAt riemannZeta ρ : ℝ) * ‖a‖
  let E : ℝ := (∑' k : ℕ, ‖actualCoeff k‖) + Real.log (2 * Real.pi)
  let phase : ℝ := a.arg + Real.pi
  let lam : ℂ := ρ - 1
  let mode (t : ℝ) : ℂ := ((C : ℂ) * Complex.exp (Complex.I * (phase : ℂ))) *
    Complex.exp (lam * (t : ℂ))
  have hρ : ρ.re < 1 := (actualData.zero_isNontrivial (actualOccurrenceEquiv p).1).2.2
  have hlameq : lam.re = ρ.re - 1 := by simp [lam]
  have hlam : lam.re < 0 := by rw [hlameq]; exact sub_neg.mpr hρ
  have hb₀ : 0 ≤ b := by linarith only [hσ, hb]
  have hb₁ : b < 1 := hbρ.trans hρ
  have hpair := actual_filtered_leading_pair μ p hmass hb₀ hbρ hγ hmoment hkill
  change a ≠ 0 ∧ 0 < C ∧ b - 1 < ρ.re - 1 ∧ 0 ≤ E ∧
    ∃ R : ℝ → ℝ, ∀ t : ℝ, Real.log 2 ≤ t →
      (∫ u : ℝ, Q (Real.exp (t + u)) ∂μ) =
        -(C * Real.exp ((ρ.re - 1) * t) * Real.cos (ρ.im * t + a.arg)) + R t ∧
      |R t| ≤ E * Real.exp ((b - 1) * t) at hpair
  obtain ⟨_, hC, _, hE, R, hR⟩ := hpair
  have hmodere (t : ℝ) :
      (mode t).re = C * Real.exp ((ρ.re - 1) * t) * Real.cos (ρ.im * t + phase) :=
    re_mode ρ C phase t
  have hphase (t : ℝ) :
      Real.cos (ρ.im * t + phase) = -Real.cos (ρ.im * t + a.arg) := by
    change Real.cos (ρ.im * t + (a.arg + Real.pi)) = _
    rw [← add_assoc, Real.cos_add_pi]
  have hperiod : 2 * Real.pi / ρ.im ≤ width := by
    apply (div_le_iff₀ hγ).2
    have hf := (div_lt_iff₀ hwidth).1 hfast
    nlinarith only [hf]
  let M : ℝ := 2 * (width + 1 / (-lam.re))
  have hlimit : Tendsto (fun t : ℝ => 2 * E * Real.exp ((b - ρ.re) * t) + C * M / t)
      atTop (𝓝 0) := by
    have hdecay := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (sub_neg.mpr hbρ))
    have he := hdecay.const_mul (2 * E)
    have hm : Tendsto (fun t : ℝ => C * M / t) atTop (𝓝 0) :=
      tendsto_id.const_div_atTop (C * M)
    simpa only [Function.comp_def, id_eq, mul_zero, zero_add] using he.add hm
  obtain ⟨T₀, hsmall⟩ := eventually_atTop.mp
    (hlimit.eventually_lt_const (half_pos hC))
  let scale : ℝ → ℝ := fun t => Real.exp ((ρ.re - 1) * t) * weight t
  have havg (t : ℝ) (ht : Real.log 2 ≤ t) (ht₀ : T₀ ≤ t) :
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν (Icc 0 width) = 1 ∧
        Integrable (fun u => Jpsi (Real.exp (t + u))) ν ∧
        |(∫ u, Jpsi (Real.exp (t + u)) ∂ν) -
          C * scale t * Real.cos (ρ.im * t + phase)| ≤ C * scale t / 2 := by
    have happrox (v : ℝ) (hv : 0 ≤ v) :
        |(∫ u, Q (Real.exp (t + v + u)) ∂μ) -
          (mode t * Complex.exp (lam * (v : ℂ))).re| ≤
          (E * Real.exp ((b - 1) * t)) * Real.exp ((b - 1) * v) := by
      have hadd : mode t * Complex.exp (lam * (v : ℂ)) = mode (t + v) := by
        simp only [mode, Complex.ofReal_add, mul_add, Complex.exp_add, mul_assoc]
      obtain ⟨heq, hbound⟩ := hR (t + v) (by linarith)
      rw [hadd, hmodere, hphase, mul_neg, heq, add_sub_cancel_left]
      rw [mul_add, Real.exp_add] at hbound
      exact hbound.trans_eq (by ring)
    obtain ⟨ν, hprob, hsupp, hestimate⟩ := exists_corrected_actual_psi_average
      hμ ht hlam (sub_neg.mpr hb₁) (mul_nonneg hE (Real.exp_pos _).le) happrox
    let _ : IsProbabilityMeasure ν := hprob
    have hν : ∀ᵐ u ∂ν, u ∈ Icc 0 width := mem_ae_iff.mpr hsupp
    refine ⟨ν, hprob, (mem_ae_iff_prob_eq_one measurableSet_Icc).mp hν,
      jpsi_integrable_average hν ht, ?_⟩
    have hleading : (mode t * (weight t : ℂ)).re =
        C * scale t * Real.cos (ρ.im * t + phase) := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hmodere]
      unfold scale
      ring
    have hscale : 0 ≤ scale t := by
      have htpos := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le ht
      unfold scale weight
      positivity
    have hfactor : Real.exp ((b - 1) * t) =
        Real.exp ((b - ρ.re) * t) * Real.exp ((ρ.re - 1) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hleading]
    refine hestimate.trans ?_
    rw [norm_mode ρ hC phase t, hfactor]
    calc
      _ = (2 * E * Real.exp ((b - ρ.re) * t) + C * M / t) * scale t := by
        unfold scale M
        ring
      _ ≤ (C / 2) * scale t := mul_le_mul_of_nonneg_right (hsmall t ht₀).le hscale
      _ = C * scale t / 2 := by ring
  let c : ℝ := C * Real.exp ((ρ.re - 1) * width) / 8
  refine ⟨ρ.re, hb.trans_lt hbρ, hρ, c, by dsimp [c]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.log 2), eventually_ge_atTop T₀,
    eventually_ge_atTop width] with T hT hT₀ hTwidth
  have hTpos : 0 < T := hwidth.trans_le hTwidth
  let lower := Real.exp ((ρ.re - 1) * (T + width)) / (2 * T)
  have hlower : 0 < lower := by dsimp [lower]; positivity
  have hscale (t : ℝ) (ht : t ∈ Icc T (T + width)) : lower ≤ scale t := by
    have htpos := hTpos.trans_le ht.1
    have hw : 1 / (2 * T) ≤ weight t := by
      have ht' : t ≤ 2 * T := by linarith [ht.2]
      calc
        _ ≤ 1 / t := one_div_le_one_div_of_le htpos ht'
        _ ≤ weight t := by
          rw [weight, le_div_iff₀ (sq_pos_of_pos htpos)]
          have heq : 1 / t * t ^ 2 = t := by field_simp
          rw [heq]
          linarith
    rw [show lower = Real.exp ((ρ.re - 1) * (T + width)) * (1 / (2 * T)) by
      dsimp [lower]; ring]
    exact mul_le_mul (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left ht.2 (sub_nonpos.mpr hρ.le)))
      hw (by positivity) (Real.exp_pos _).le
  have hvalue := PositiveAverageCosineWindow.exists_signed_values
    (f := fun t => Jpsi (Real.exp t)) (start := T) (support := width) (phase := phase)
    hγ hperiod hC hlower hscale
    (fun t ht => havg t (hT.trans ht.1) (hT₀.trans ht.1))
  have hend : T + width + width = T + h := by dsimp [width]; ring
  have hlevel : C * lower / 4 = c * Real.exp ((ρ.re - 1) * T) / T := by
    dsimp only [lower, c]
    rw [mul_add, Real.exp_add]
    ring
  simpa only [hend, hlevel] using hvalue

end D5.S3.Arith.Robin.Analytic.ActualUnattainedWeightedWindows
