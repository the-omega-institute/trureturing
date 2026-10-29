/- GID: D5/S3/Weil/Mertens/ThetaTailZeroExclusion
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/ThetaTailZeroExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Meromorphic.Order]
   utility: none
   digest: Actual theta-tail exponential domination contradicts every zeta zero in the corresponding right half-plane. -/

import D5.S3.Weil.Mertens.ActualThetaTailLaplace
import D5.S3.Analytic.Laplace.PositiveEulerContinuation
import D5.S3.Analytic.Isolation.RiemannZetaPositiveRealSign
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace D5.S3.Weil.Mertens.ThetaTailZeroExclusion

open Real Set MeasureTheory Filter ProbabilityTheory Complex
open scoped Topology

noncomputable section

open ActualThetaTailLaplace
open ThetaLaplaceContinuation
open D5.S3.Analytic.Laplace.PositiveEulerContinuation
open D5.S3.Analytic.Isolation.RiemannZetaPositiveRealSign

private def K (U b C : ℝ) (s : ℂ) : ℂ :=
  (C : ℂ) * Complex.exp (-(s + b) * (U : ℂ)) / (s + b)

private def euler (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  s * deriv (deriv F) s + 2 * deriv F s

private def forcing (U b C : ℝ) (s : ℂ) : ℂ :=
  euler (K U b C) s - (-deriv (M U) s + M U s) -
    (U : ℂ) ^ 2 * (f U : ℂ) * Complex.exp (-s * (U : ℂ))

private lemma u₀_nonneg : 0 ≤ u₀ := le_of_lt (Real.log_pos (by norm_num))

private lemma exp_weight_integrable {U b : ℝ} (hb : 0 < b) (hU : u₀ ≤ U) :
    IntegrableOn (fun u : ℝ => Real.exp (-b * u)) (Ioi U) := by
  have h := integrableOn_exp_mul_Ioi (a := -b) (by linarith) U
  simpa [mul_comm] using h

private lemma forcing_domain_subset {b : ℝ} (hb : b < 1 / 2) :
    {z : ℂ | -b < z.re} ⊆ ThetaLaplaceContinuation.D := by
  intro z hz
  change -(1 / 2 : ℝ) < z.re
  change -b < z.re at hz
  linarith

private lemma K_analytic {U b C : ℝ} (hb : 0 < b) :
    AnalyticOnNhd ℂ (K U b C) {z : ℂ | -b < z.re} := by
  intro z hz
  have hden : (z + b) ≠ 0 := by
    intro h
    have : (z + b).re = 0 := by rw [h]; simp
    simp only [add_re, ofReal_re] at this
    change -b < z.re at hz
    linarith
  exact ((analyticAt_const.mul
      ((analyticAt_id.add analyticAt_const).neg.mul analyticAt_const).cexp).div
      (analyticAt_id.add analyticAt_const) hden)

private lemma K_real_integral {U b C : ℝ} {s : ℂ} (hb : 0 < b)
    (hs : 0 < s.re) :
    (∫ u in Ioi U, Complex.exp (-s * (u : ℂ)) *
      (C * Real.exp (-b * u) : ℂ)) = K U b C s := by
  have ha : (-(s + b)).re < 0 := by
    simp only [neg_re, add_re, ofReal_re]
    linarith
  have hi := integral_exp_mul_complex_Ioi ha U
  have hcalc :
      (∫ u in Ioi U, Complex.exp (-(s + b) * (u : ℂ))) =
        -Complex.exp (-(s + b) * (U : ℂ)) / (-(s + b)) := hi
  rw [show (fun u : ℝ => Complex.exp (-s * (u : ℂ)) *
      (C * Real.exp (-b * u) : ℂ)) =
      (fun u : ℝ => (C : ℂ) * Complex.exp (-(s + b) * (u : ℂ))) by
        funext u
        calc
          Complex.exp (-s * (u : ℂ)) * (C * Real.exp (-b * u) : ℂ) =
              (C : ℂ) * (Complex.exp (-s * (u : ℂ)) *
                Complex.exp ((-(b * u) : ℝ) : ℂ)) := by
                  simp only [Complex.ofReal_exp]
                  ring
          _ = (C : ℂ) * Complex.exp
              ((-s * (u : ℂ)) + ((-(b * u) : ℝ) : ℂ)) := by
                rw [← Complex.exp_add]
          _ = (C : ℂ) * Complex.exp (-(s + b) * (u : ℂ)) := by
                congr 2
                push_cast
                ring_nf]
  rw [integral_const_mul, hcalc]
  dsimp [K]
  field_simp

private lemma M_real_analytic {v b : ℝ} (hv : 0 ≤ v) (hb : b < 1 / 2) :
    ∀ x : ℝ, -b < x → AnalyticAt ℂ (M v) (x : ℂ) := by
  intro x hx
  by_cases hx0 : x = 0
  · simpa [hx0] using
      (ThetaLaplaceContinuation.theta_laplace_continuation v hv).2.2.2.2.2.1
  have hzpos : 0 < 1 + x := by linarith
  have hz1 : (1 + x : ℝ) ≠ 1 := by
    intro h
    apply hx0
    linarith
  have hsign := riemannZeta_ofReal_sign hzpos hz1
  have hzeta : riemannZeta ((1 + x : ℝ) : ℂ) ≠ 0 := by
    intro h
    have : (riemannZeta ((1 + x : ℝ) : ℂ)).re = 0 := by rw [h]; simp
    rcases hsign.2 with hbelow | habove
    · linarith
    · linarith
  have hnorm : riemannZeta₁ ((1 + x : ℝ) : ℂ) ≠ 0 := by
    intro hn
    have he := riemannZeta_eq_inv_sub_mul
      (show ((1 + x : ℝ) : ℂ) ≠ 1 by simpa using hz1)
    rw [hn, mul_zero] at he
    exact hzeta he
  have hz : AnalyticAt ℂ (fun z : ℂ => logDeriv riemannZeta₁ (1 + z)) (x : ℂ) :=
    (show AnalyticAt ℂ (fun z : ℂ =>
      deriv riemannZeta₁ z / riemannZeta₁ z) ((1 + x : ℝ) : ℂ) from
      (differentiable_riemannZeta₁.analyticAt ((1 + x : ℝ) : ℂ)).deriv.div
        (differentiable_riemannZeta₁.analyticAt ((1 + x : ℝ) : ℂ)) hnorm).comp_of_eq
      (by fun_prop) (by norm_num)
  have hc : AnalyticAt ℂ (fun z : ℂ => C (1 + z)) (x : ℂ) :=
    ((ThetaLaplaceContinuation.theta_laplace_continuation v hv).1
      ((1 + x : ℝ) : ℂ) (by change (1 / 2 : ℝ) < (1 + x : ℝ); linarith)).comp_of_eq
      (by fun_prop) (by norm_num)
  have ha : AnalyticAt ℂ (fun z : ℂ => A v z) (x : ℂ) :=
    (ThetaLaplaceContinuation.theta_laplace_continuation v hv).2.1.analyticAt x
  unfold M
  have hden : (1 + (x : ℂ)) ≠ 0 := by
    intro h
    have : (1 + x : ℝ) = 0 := by exact_mod_cast h
    linarith
  exact (((analyticAt_const.add hz).add hc).neg.div (by fun_prop) hden).sub ha

private lemma forcing_meromorphic {b C U : ℝ} (hb : 0 < b) (hb2 : b < 1 / 2)
    (hU : u₀ ≤ U) :
    MeromorphicOn (forcing U b C) {z : ℂ | -b < z.re} := by
  intro z hz
  have hU0 : 0 ≤ U := le_trans u₀_nonneg hU
  have hD := ThetaLaplaceContinuation.theta_laplace_continuation U hU0
  have hM := hD.2.2.2.2.1 z (forcing_domain_subset hb2 hz)
  have hK := (K_analytic (U := U) (b := b) (C := C) hb z hz).meromorphicAt
  have hE : MeromorphicAt (euler (K U b C)) z := by
    exact ((analyticAt_id.meromorphicAt.mul hK.deriv.deriv).add
      ((analyticAt_const.meromorphicAt).mul hK.deriv))
  have hF : MeromorphicAt (fun s => -deriv (M U) s + M U s) z :=
    hM.deriv.neg.add hM
  have hB : MeromorphicAt (fun s : ℂ =>
      (U : ℂ) ^ 2 * (f U : ℂ) * Complex.exp (-s * (U : ℂ))) z := by fun_prop
  exact (hE.sub hF).sub hB

private lemma forcing_real_analytic {b C U : ℝ} (hb : 0 < b) (hb2 : b < 1 / 2)
    (hU : u₀ ≤ U) :
    ∀ x : ℝ, -b < x → AnalyticAt ℂ (forcing U b C) (x : ℂ) := by
  intro x hx
  have hK := K_analytic (U := U) (b := b) (C := C) hb (x : ℂ) (by simpa using hx)
  have hU0 : 0 ≤ U := le_trans u₀_nonneg hU
  have hM := M_real_analytic hU0 hb2 x hx
  have hB : AnalyticAt ℂ (fun s : ℂ =>
        (U : ℂ) ^ 2 * (f U : ℂ) * Complex.exp (-s * (U : ℂ))) (x : ℂ) := by fun_prop
  exact ((analyticAt_id.mul hK.deriv.deriv).add
    (analyticAt_const.mul hK.deriv)).sub (hM.deriv.neg.add hM) |>.sub hB

private lemma tail_zero_exclusion {b C : ℝ} (hb : 0 < b) (hb2 : b < 1 / 2)
    (hC : 0 ≤ C) (hbound : ∀ᶠ u : ℝ in atTop, f u ≤ C * Real.exp (-b * u)) :
    ∀ ρ : ℂ, 1 - b < ρ.re → riemannZeta ρ ≠ 0 := by
  intro ρ hρ
  by_contra hzρ
  obtain ⟨V, hV⟩ := (eventually_atTop.1 hbound)
  let U : ℝ := max u₀ V
  have hU : u₀ ≤ U := le_max_left _ _
  have hU0 : 0 ≤ U := le_trans u₀_nonneg hU
  have hUV : V ≤ U := le_max_right _ _
  have hdom : ∀ᵐ u ∂volume.restrict (Ioi U), 0 ≤ C * Real.exp (-b * u) - f u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have huV : V ≤ u := le_trans hUV hu.le
    linarith [hV u huV]
  let base : Measure ℝ := volume.restrict (Ioi U)
  let density : ℝ → ENNReal := fun u => ENNReal.ofReal (C * Real.exp (-b * u) - f u)
  let μ : Measure ℝ := base.withDensity density
  obtain ⟨⟨hqsm, hqfi⟩, ⟨hksm, hkfi⟩, horig, hident, hf0, htailbound,
      hftendsto, hfac, hfae, hLaplace⟩ := actual_theta_tail_laplace_ode
  have hf : IntegrableOn f (Ioi U) := hf0.mono_set (Ioi_subset_Ioi hU)
  have he : IntegrableOn (fun u : ℝ => C * Real.exp (-b * u)) (Ioi U) := by
    simpa [IntegrableOn, mul_comm] using (exp_weight_integrable hb hU).const_mul C
  have hg : IntegrableOn (fun u : ℝ => C * Real.exp (-b * u) - f u) (Ioi U) := by
    exact (he.sub hf)
  have hgfin : HasFiniteIntegral (fun u : ℝ => C * Real.exp (-b * u) - f u) base := by
    simpa only [HasFiniteIntegral, IntegrableOn] using hg.hasFiniteIntegral
  letI : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hgfin
  have hdens : AEMeasurable density base := by
    exact (he.aemeasurable.sub hf.aemeasurable).ennreal_ofReal
  have hX : AEMeasurable (id : ℝ → ℝ) μ :=
    (measurable_id.aemeasurable.mono_ac (withDensity_absolutelyContinuous _ _))
  have hXnonneg_base : ∀ᵐ u ∂base, 0 ≤ id u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact le_trans (le_of_lt (Real.log_pos (by norm_num))) (le_trans hU hu.le)
  have hXnonneg : ∀ᵐ u ∂μ, 0 ≤ id u :=
    hXnonneg_base.filter_mono (withDensity_absolutelyContinuous _ _).ae_le
  have hGid : ∀ s : ℂ, 0 < s.re →
      complexMGF id μ (-s) = K U b C s - L U s := by
    intro s hs
    rw [complexMGF]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hdens
      (Filter.Eventually.of_forall (fun u => ENNReal.ofReal_lt_top))]
    have hto : ∀ᵐ u ∂base, (density u).toReal = C * Real.exp (-b * u) - f u := by
      filter_upwards [hdom] with u hu
      have hnon : 0 ≤ C * Real.exp (-b * u) - f u := hu
      change (ENNReal.ofReal (C * Real.exp (-b * u) - f u)).toReal = _
      rw [ENNReal.toReal_ofReal hnon]
    have hsplit :
        (∫ u, (density u).toReal • Complex.exp (-s * (id u : ℂ)) ∂base) =
          (∫ u in Ioi U, Complex.exp (-s * (u : ℂ)) *
            (C * Real.exp (-b * u) : ℂ)) - L U s := by
      rw [show base = volume.restrict (Ioi U) by rfl]
      have hrewrite :
          (fun u : ℝ => (density u).toReal • Complex.exp (-s * (id u : ℂ))) =ᵐ[volume.restrict (Ioi U)]
            (fun u => ((C * Real.exp (-b * u) - f u : ℝ) : ℂ) *
              Complex.exp (-s * (u : ℂ))) := by
        filter_upwards [hto] with u hu
        simp only [id_eq, smul_eq_mul]
        rw [hu]
        norm_cast
      rw [integral_congr_ae hrewrite]
      change
        (∫ u in Ioi U, ((C * Real.exp (-b * u) - f u : ℝ) : ℂ) *
          Complex.exp (-s * (u : ℂ))) =
          (∫ u in Ioi U, Complex.exp (-s * (u : ℂ)) *
            (C * Real.exp (-b * u) : ℂ)) -
            (∫ u in Ioi U, Complex.exp (-s * (u : ℂ)) * (f u : ℂ))
      have hCint : IntegrableOn
          (fun u : ℝ => Complex.exp (-s * (u : ℂ)) *
            (C * Real.exp (-b * u) : ℂ)) (Ioi U) := by
        have hbase : IntegrableOn (fun u : ℝ => (C * Real.exp (-b * u) : ℂ))
            (Ioi U) := by
          convert (IntegrableOn.ofReal (𝕜 := ℂ) he) using 1
          funext u
          rw [← Complex.ofReal_mul]
          rfl
        have hexp : AEStronglyMeasurable
            (fun u : ℝ => Complex.exp (-s * (u : ℂ)))
            (volume.restrict (Ioi U)) := by fun_prop
        have hboundexp : ∀ᵐ u : ℝ ∂(volume.restrict (Ioi U)),
            ‖Complex.exp (-s * (u : ℂ))‖ ≤ (1 : ℝ) := by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          rw [Complex.norm_exp]
          simp only [Complex.neg_re, Complex.mul_re, ofReal_re, ofReal_im, mul_zero,
            sub_zero]
          rw [Real.exp_le_one_iff]
          have hprod : 0 ≤ s.re * u :=
            mul_nonneg (le_of_lt hs) (le_trans hU0 hu.le)
          simpa [neg_mul] using (neg_nonpos.mpr hprod)
        simpa [IntegrableOn, mul_comm] using hbase.mul_bdd hexp hboundexp
      have hfint : IntegrableOn
          (fun u : ℝ => Complex.exp (-s * (u : ℂ)) * (f u : ℂ)) (Ioi U) := by
        have hbase : IntegrableOn (fun u : ℝ => (f u : ℂ)) (Ioi U) := hf.ofReal
        have hexp : AEStronglyMeasurable
            (fun u : ℝ => Complex.exp (-s * (u : ℂ)))
            (volume.restrict (Ioi U)) := by fun_prop
        have hboundexp : ∀ᵐ u : ℝ ∂(volume.restrict (Ioi U)),
            ‖Complex.exp (-s * (u : ℂ))‖ ≤ (1 : ℝ) := by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          rw [Complex.norm_exp]
          simp only [Complex.neg_re, Complex.mul_re, ofReal_re, ofReal_im, mul_zero,
            sub_zero]
          rw [Real.exp_le_one_iff]
          have hprod : 0 ≤ s.re * u :=
            mul_nonneg (le_of_lt hs) (le_trans hU0 hu.le)
          simpa [neg_mul] using (neg_nonpos.mpr hprod)
        simpa [IntegrableOn, mul_comm] using hbase.mul_bdd hexp hboundexp
      rw [← integral_sub hCint hfint]
      congr 1
      funext u
      push_cast
      ring
    have hsplit' :
        (∫ u, (density u).toReal • Complex.exp (-s * (id u : ℂ)) ∂base) =
          K U b C s - L U s := by
      calc
        _ = (∫ u in Ioi U, Complex.exp (-s * (u : ℂ)) *
            (C * Real.exp (-b * u) : ℂ)) - L U s := hsplit
        _ = K U b C s - L U s := by rw [K_real_integral hb hs]
    simpa [id_eq] using hsplit'
  have hode : ∀ z : ℂ, 0 < z.re →
      z * deriv (deriv (fun w => complexMGF id μ (-w))) z +
        2 * deriv (fun w => complexMGF id μ (-w)) z = forcing U b C z := by
    intro z hz
    have hQU := hLaplace U hU
    have hQ := hQU.2 z hz
    have hQM :=
      (ThetaLaplaceContinuation.theta_laplace_continuation U hU0).2.2.2.1 z hz
    have hEq : (fun w : ℂ => complexMGF id μ (-w)) =ᶠ[𝓝 z]
        (fun w => K U b C w - L U w) :=
      by
        filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hz]
          with w hw
        exact hGid w hw
    have hK := K_analytic (U := U) (b := b) (C := C) hb z
      (by change -b < z.re; linarith)
    have hL := hQU.1 z hz
    have hKL := hK.sub hL
    have hG1 : HasDerivAt (fun w : ℂ => complexMGF id μ (-w))
        (deriv (fun w => K U b C w - L U w) z) z := by
      exact hKL.differentiableAt.hasDerivAt.congr_of_eventuallyEq hEq
    have hG2 : HasDerivAt (deriv (fun w : ℂ => complexMGF id μ (-w)))
        (deriv (deriv (fun w => K U b C w - L U w)) z) z := by
      exact hKL.deriv.differentiableAt.hasDerivAt.congr_of_eventuallyEq hEq.deriv
    rw [hG1.deriv, hG2.deriv]
    dsimp [forcing, euler]
    have hLode := hQ.2.2.2
    have hEqQM : Q U =ᶠ[𝓝 z] M U := by
      filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hz]
        with w hw
      exact (ThetaLaplaceContinuation.theta_laplace_continuation U hU0).2.2.2.1 w hw |>.2.1
    have hMder := hQM.2.2.2.congr_of_eventuallyEq hEqQM.symm
    have hderQM : deriv (Q U) z = deriv (M U) z := by
      rw [hQM.2.2.2.deriv, hMder.deriv]
    have hodeM : z * deriv (deriv (L U)) z + 2 * deriv (L U) z =
        -deriv (M U) z + M U z +
          (U : ℂ) ^ 2 * (f U : ℂ) * Complex.exp (-z * (U : ℂ)) := by
      calc
        _ = -deriv (Q U) z + Q U z +
            (U : ℂ) ^ 2 * (f U : ℂ) * Complex.exp (-z * (U : ℂ)) := hLode
        _ = _ := by rw [hderQM, hQM.2.1]
    rw [deriv_fun_sub hK.differentiableAt hL.differentiableAt]
    have hsecond :
        deriv (deriv (fun w => K U b C w - L U w)) z =
          deriv (deriv (K U b C)) z - deriv (deriv (L U)) z := by
      have heq : deriv (fun w => K U b C w - L U w) =ᶠ[𝓝 z]
          (fun w => deriv (K U b C) w - deriv (L U) w) := by
        filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hz]
          with w hw
        exact deriv_fun_sub
          (K_analytic (U := U) (b := b) (C := C) hb w (by change -b < w.re; linarith)
            |>.differentiableAt)
          (hQU.1 w hw |>.differentiableAt)
      calc
        _ = deriv (fun w => deriv (K U b C) w - deriv (L U) w) z := heq.deriv_eq
        _ = _ := deriv_fun_sub hK.deriv.differentiableAt hL.deriv.differentiableAt
    rw [hsecond]
    calc
      _ = z * deriv (deriv (K U b C)) z + 2 * deriv (K U b C) z -
          (z * deriv (deriv (L U)) z + 2 * deriv (L U) z) := by ring
      _ = _ := by rw [hodeM]; ring
  have hcont := integrable_and_analytic_of_euler hX hXnonneg (show -b < 0 by linarith)
    (forcing_meromorphic hb hb2 hU) (forcing_real_analytic hb hb2 hU) hode
  have hGanalytic : AnalyticOnNhd ℂ (fun z => complexMGF id μ (-z))
      {z | -b < z.re} := hcont.2
  have hKanalytic := K_analytic (U := U) (b := b) (C := C) hb
  have hHanalytic : AnalyticOnNhd ℂ (fun z => K U b C z - complexMGF id μ (-z))
      {z | -b < z.re} := hKanalytic.sub hGanalytic
  have hEanalytic : AnalyticOnNhd ℂ
      (fun z => euler (fun w => K U b C w - complexMGF id μ (-w)) z -
        (U : ℂ) ^ 2 * (f U : ℂ) * Complex.exp (-z * (U : ℂ)))
      {z | -b < z.re} := by
    intro z hz
    have hH := hHanalytic z hz
    have hB : AnalyticAt ℂ (fun s : ℂ =>
        (U : ℂ) ^ 2 * (f U : ℂ) * Complex.exp (-s * (U : ℂ))) z := by fun_prop
    exact ((analyticAt_id.mul hH.deriv.deriv).add
      (analyticAt_const.mul hH.deriv)).sub hB
  let E : ℂ → ℂ := fun z => euler (fun w => K U b C w - complexMGF id μ (-w)) z -
      (U : ℂ) ^ 2 * (f U : ℂ) * Complex.exp (-z * (U : ℂ))
  let R : ℂ → ℂ := forcing U b C
  have hFmer : MeromorphicOn (fun z => -deriv (M U) z + M U z)
      {z | -b < z.re} := by
    intro z hz
    have hU0 : 0 ≤ U := le_trans u₀_nonneg hU
    have hM := (ThetaLaplaceContinuation.theta_laplace_continuation U hU0).2.2.2.2.1
      z (forcing_domain_subset hb2 hz)
    exact hM.deriv.neg.add hM
  have hdiff : MeromorphicOn (fun z => E z - (-deriv (M U) z + M U z))
      {z | -b < z.re} := by
    exact hEanalytic.meromorphicOn.sub hFmer
  have hzero_one : meromorphicOrderAt
      (fun z => E z - (-deriv (M U) z + M U z)) (1 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have h1 : (1 : ℂ) ∈ {z : ℂ | 0 < z.re} := by norm_num
    have hEv : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), z ∈ {z : ℂ | 0 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds h1
    filter_upwards [hEv.filter_mono nhdsWithin_le_nhds]
      with z hzpos
    have hz : -b < z.re := by linarith
    have hQ := (hLaplace U hU).2 z hzpos
    have hM :=
      (ThetaLaplaceContinuation.theta_laplace_continuation U hU0).2.2.2.1 z hzpos
    have hEqH : (fun w : ℂ => K U b C w - complexMGF id μ (-w)) =ᶠ[𝓝 z]
        (fun w => L U w) := by
      filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hzpos]
        with w hw
      rw [hGid w hw]
      ring
    have hL1 := hQ.2.1
    have hH1 : HasDerivAt (fun w : ℂ => K U b C w - complexMGF id μ (-w))
        (deriv (L U) z) z := by
      exact (hL1.congr_of_eventuallyEq hEqH).congr_deriv hQ.2.1.deriv.symm
    have hH2 : HasDerivAt
        (deriv (fun w : ℂ => K U b C w - complexMGF id μ (-w)))
        (deriv (deriv (L U)) z) z := by
      exact (hQ.2.2.1.congr_of_eventuallyEq hEqH.deriv).congr_deriv
        hQ.2.2.1.deriv.symm
    have hEqQM : Q U =ᶠ[𝓝 z] M U := by
      filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hzpos]
        with w hw
      exact (ThetaLaplaceContinuation.theta_laplace_continuation U hU0).2.2.2.1 w hw |>.2.1
    have hMder := hM.2.2.2.congr_of_eventuallyEq hEqQM.symm
    have hderQM : deriv (Q U) z = deriv (M U) z := by
      rw [hM.2.2.2.deriv, hMder.deriv]
    have hodeM : z * deriv (deriv (L U)) z + 2 * deriv (L U) z =
        -deriv (M U) z + M U z +
          (U : ℂ) ^ 2 * (f U : ℂ) * Complex.exp (-z * (U : ℂ)) := by
      calc
        _ = -deriv (Q U) z + Q U z +
            (U : ℂ) ^ 2 * (f U : ℂ) * Complex.exp (-z * (U : ℂ)) := hQ.2.2.2
        _ = _ := by rw [hderQM, hM.2.1]
    dsimp [E, forcing, euler]
    rw [hH1.deriv, hH2.deriv]
    linear_combination hodeM
  have hdompre : IsPreconnected {z : ℂ | -b < z.re} :=
    (convex_halfSpace_re_gt (-b)).isPreconnected
  have ha : 1 - b < ρ.re := hρ
  let a : ℂ := ρ - 1
  have haD : a ∈ {z : ℂ | -b < z.re} := by
    change -b < (ρ - 1).re
    simp only [sub_re, one_re]
    linarith
  have htop := hdiff.meromorphicOrderAt_eq_top_of_isPreconnected hdompre
    (show (1 : ℂ) ∈ {z : ℂ | -b < z.re} by change -b < (1 : ℝ); linarith)
    haD hzero_one
  have hp :=
    (ThetaLaplaceContinuation.theta_laplace_continuation U hU0).2.2.2.2.2.2.2 ρ
      (by linarith) hzρ
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, hForder⟩
  have hpunct := meromorphicOrderAt_eq_top_iff.mp htop
  have hEqgerm : E =ᶠ[𝓝[≠] a] (fun z => -deriv (M U) z + M U z) := by
    filter_upwards [hpunct] with z hz
    exact sub_eq_zero.mp hz
  have hEorder : 0 ≤ meromorphicOrderAt E a :=
    (hEanalytic a haD).meromorphicOrderAt_nonneg
  have horderEq : meromorphicOrderAt E a =
      meromorphicOrderAt (fun z => -deriv (M U) z + M U z) a :=
    meromorphicOrderAt_congr hEqgerm
  rw [hForder] at horderEq
  rw [horderEq] at hEorder
  have hbad' : (0 : ℤ) ≤ (-2 : ℤ) := WithTop.coe_le_coe.mp hEorder
  omega

theorem actual_theta_tail_exponential_zero_exclusion {b C : ℝ}
    (hb : 0 < b) (hb2 : b < 1 / 2) (hC : 0 ≤ C)
    (hbound : ∀ᶠ u : ℝ in atTop, f u ≤ C * Real.exp (-b * u)) :
    ∀ ρ : ℂ, 1 - b < ρ.re → riemannZeta ρ ≠ 0 := by
  exact tail_zero_exclusion hb hb2 hC hbound

#print axioms actual_theta_tail_exponential_zero_exclusion

end
end D5.S3.Weil.Mertens.ThetaTailZeroExclusion
