/- GID: D5/S3/Analytic/Adelic/GlobalLogarithmicGaugeCriterion
   generality: I
   mirror-B: D5/B/S3/Analytic/Adelic/GlobalLogarithmicGaugeCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Global analytic logarithms of shifted xi characterize the critical line. -/

import D5.S3.Weil.ZetaRvm.CountByIntegral
import D5.S3.Zeros.CompletedZeta
import D5.S3.Zeros.Endpoints.XiEndpointValues
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Tactic

/- Library-search audit trail (2026-08-31):
   * Repository searches for a global analytic logarithm criterion, exponential
     lifts, and logarithmic phase gauges found no exact frozen theorem. The
     completed-zeta reading, its zero criterion, endpoint values, and reflection
     are imported as the canonical source carrier.
   * Body-shape searches for an imaginary differential built from `fderiv`,
     `restrictScalars`, and `Complex.imCLM.comp` found no D5 primitive.
   * Pinned Mathlib has no exact analytic-logarithm theorem. Its Poincare
     primitive theorem and logarithmic-derivative characterization construct the
     logarithm used below; `BranchLogRoot` provides only a continuous lift.
   * Searches of installed packages and the public Lean ecosystem found no exact
     theorem on this carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex Set

namespace D5.S3.Analytic.Adelic.GlobalLogarithmicGaugeCriterion

private theorem exists_analytic_log_on_open_convex
    {U : Set ℂ} (hUo : IsOpen U) (hUc : Convex ℝ U) (hUne : U.Nonempty)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hgn : ∀ z ∈ U, g z ≠ 0) :
    ∃ L : ℂ → ℂ,
      AnalyticOnNhd ℂ L U ∧ EqOn (Complex.exp ∘ L) g U := by
  have hgDiff : DifferentiableOn ℂ g U := hg.differentiableOn
  have hDerivDiff : DifferentiableOn ℂ (deriv g) U := hgDiff.deriv hUo
  have hLogDerivDiff : DifferentiableOn ℂ (logDeriv g) U := by
    change DifferentiableOn ℂ (deriv g / g) U
    exact hDerivDiff.div hgDiff hgn
  obtain ⟨P, hPWithin⟩ := hUc.exists_forall_hasDerivWithinAt hLogDerivDiff
  have hP : ∀ z ∈ U, HasDerivAt P (logDeriv g z) z := by
    intro z hz
    exact (hPWithin z hz).hasDerivAt (hUo.mem_nhds hz)
  obtain ⟨z₀, hz₀⟩ := hUne
  let L : ℂ → ℂ := fun z ↦ P z - P z₀ + Complex.log (g z₀)
  have hL : ∀ z ∈ U, HasDerivAt L (logDeriv g z) z := by
    intro z hz
    simpa only [L] using
      (hP z hz).sub_const (P z₀) |>.add_const (Complex.log (g z₀))
  have hLDiff : DifferentiableOn ℂ L U :=
    fun z hz ↦ (hL z hz).differentiableAt.differentiableWithinAt
  have hExpDiff : DifferentiableOn ℂ (Complex.exp ∘ L) U := by
    intro z hz
    exact ((hL z hz).cexp).differentiableAt.differentiableWithinAt
  have hExpNonzero : ∀ z ∈ U, (Complex.exp ∘ L) z ≠ 0 := by
    intro z _
    exact Complex.exp_ne_zero _
  have hLogDerivEq : EqOn (logDeriv (Complex.exp ∘ L)) (logDeriv g) U := by
    intro z hz
    rw [logDeriv_apply, logDeriv_apply]
    have hExpDeriv := ((hL z hz).cexp).deriv
    change deriv (fun x ↦ Complex.exp (L x)) z / Complex.exp (L z) =
      deriv g z / g z
    rw [hExpDeriv]
    field_simp [Complex.exp_ne_zero]
    exact logDeriv_apply g z
  obtain ⟨c, hc, hEq⟩ :=
    (logDeriv_eqOn_iff hExpDiff hgDiff hUo hUc.isPreconnected hgn hExpNonzero).mp
      hLogDerivEq
  have hAtBase : (Complex.exp ∘ L) z₀ = g z₀ := by
    simp only [Function.comp_apply, L, sub_self, zero_add]
    exact Complex.exp_log (hgn z₀ hz₀)
  have hcOne : c = 1 := by
    have hEqBase := hEq hz₀
    rw [hAtBase] at hEqBase
    simp only [Pi.smul_apply, smul_eq_mul] at hEqBase
    exact (mul_eq_right₀ (hgn z₀ hz₀)).mp hEqBase.symm
  refine ⟨L, hLDiff.analyticOnNhd hUo, ?_⟩
  intro z hz
  simpa only [hcOne, one_smul] using hEq hz

private theorem phase_gauge_continuous
    {U : Set ℂ} (hUo : IsOpen U) {L : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L U) :
    ContinuousOn
      (fun z ↦ Complex.imCLM.comp ((fderiv ℂ L z).restrictScalars ℝ)) U := by
  have hSmooth : ContDiffOn ℂ ⊤ L U := hL.contDiffOn_of_completeSpace
  have hFDeriv : ContinuousOn (fderiv ℂ L) U :=
    hSmooth.continuousOn_fderiv_of_isOpen hUo (by simp)
  let gaugeMap : (ℂ →L[ℂ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.imCLM).comp
      (ContinuousLinearMap.restrictScalarsL ℂ ℂ ℂ ℝ ℝ)
  have hGauge := gaugeMap.continuous.comp_continuousOn hFDeriv
  refine hGauge.congr ?_
  intro z hz
  rfl

open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Endpoints.XiEndpointValues
open Zeta23 Zeta23.RvM

/--
The critical-line criterion is equivalent to the existence of a global
analytic logarithm of the shifted completed-zeta reading on the right
half-plane. Under that criterion its imaginary differential is continuous on
the whole domain. A zero obstructs a global logarithm and is excluded from
every domain on which an exponential lift exists.
-/
theorem global_logarithmic_gauge_criterion :
    let rightHalfPlane : Set ℂ := {z | 0 < z.re}
    let shiftedXi : ℂ → ℂ := fun z ↦ xiReading ((1 / 2 : ℂ) + z)
    let criticalLineHypothesis : Prop :=
      ∀ s : ℂ, IsNontrivialZero s → s.re = (1 : ℝ) / 2
    (criticalLineHypothesis ↔
      ∃ L : ℂ → ℂ,
        AnalyticOnNhd ℂ L rightHalfPlane ∧
        EqOn (Complex.exp ∘ L) shiftedXi rightHalfPlane) ∧
    (criticalLineHypothesis →
      ∃ L : ℂ → ℂ,
        AnalyticOnNhd ℂ L rightHalfPlane ∧
        EqOn (Complex.exp ∘ L) shiftedXi rightHalfPlane ∧
        ContinuousOn
          (fun z ↦ Complex.imCLM.comp
            ((fderiv ℂ L z).restrictScalars ℝ)) rightHalfPlane) ∧
    (∀ z₀ ∈ rightHalfPlane, shiftedXi z₀ = 0 →
      (¬ ∃ L : ℂ → ℂ,
        AnalyticOnNhd ℂ L rightHalfPlane ∧
        EqOn (Complex.exp ∘ L) shiftedXi rightHalfPlane) ∧
      ∀ (domain : Set ℂ) (L : ℂ → ℂ),
        EqOn (Complex.exp ∘ L) shiftedXi domain → z₀ ∉ domain) := by
  dsimp only
  let rightHalfPlane : Set ℂ := {z | 0 < z.re}
  let shiftedXi : ℂ → ℂ := fun z ↦ xiReading ((1 / 2 : ℂ) + z)
  let criticalLineHypothesis : Prop :=
    ∀ s : ℂ, IsNontrivialZero s → s.re = (1 : ℝ) / 2
  change (criticalLineHypothesis ↔
      ∃ L : ℂ → ℂ,
        AnalyticOnNhd ℂ L rightHalfPlane ∧
        EqOn (Complex.exp ∘ L) shiftedXi rightHalfPlane) ∧
    (criticalLineHypothesis →
      ∃ L : ℂ → ℂ,
        AnalyticOnNhd ℂ L rightHalfPlane ∧
        EqOn (Complex.exp ∘ L) shiftedXi rightHalfPlane ∧
        ContinuousOn
          (fun z ↦ Complex.imCLM.comp
            ((fderiv ℂ L z).restrictScalars ℝ)) rightHalfPlane) ∧
    (∀ z₀ ∈ rightHalfPlane, shiftedXi z₀ = 0 →
      (¬ ∃ L : ℂ → ℂ,
        AnalyticOnNhd ℂ L rightHalfPlane ∧
        EqOn (Complex.exp ∘ L) shiftedXi rightHalfPlane) ∧
      ∀ (domain : Set ℂ) (L : ℂ → ℂ),
        EqOn (Complex.exp ∘ L) shiftedXi domain → z₀ ∉ domain)
  have hOpen : IsOpen rightHalfPlane := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hConvex : Convex ℝ rightHalfPlane := by
    exact convex_halfSpace_gt Complex.reLm.isLinear 0
  have hNonempty : rightHalfPlane.Nonempty := by
    exact ⟨1, by norm_num [rightHalfPlane]⟩
  have hAnalytic : AnalyticOnNhd ℂ shiftedXi rightHalfPlane := by
    intro z hz
    exact (xi_reading_differentiable.analyticAt _).comp
      (analyticAt_const.add analyticAt_id)
  have xiNonzeroOfCritical (hCritical : criticalLineHypothesis) :
      ∀ z ∈ rightHalfPlane, shiftedXi z ≠ 0 := by
    intro z hz hXi
    let s : ℂ := (1 / 2 : ℂ) + z
    have hsRe : (1 : ℝ) / 2 < s.re := by
      change 0 < z.re at hz
      norm_num [s]
      linarith
    have hsZero : s ≠ 0 := by
      intro hs
      rw [hs] at hsRe
      norm_num at hsRe
    have hsOne : s ≠ 1 := by
      intro hs
      have hEndpoint : xiReading s = (1 / 2 : ℂ) := by
        rw [hs]
        exact xi_reading_endpoint_values.2
      change xiReading s = 0 at hXi
      rw [hEndpoint] at hXi
      norm_num at hXi
    have hProduct := xi_reading_eq_completed_zeta hsZero hsOne
    change xiReading s = 0 at hXi
    rw [hXi] at hProduct
    have hCompleted : completedRiemannZeta s = 0 := by
      change completedZetaReading s = 0
      apply (mul_eq_zero.mp hProduct.symm).resolve_left
      exact mul_ne_zero
        (mul_ne_zero (by norm_num) hsZero)
        (sub_ne_zero.mpr hsOne)
    have hNontrivial : IsNontrivialZero s :=
      completedRiemannZeta_eq_zero_iff.mp hCompleted
    exact (ne_of_gt hsRe) (hCritical s hNontrivial)
  have criticalOfGlobalLog
      (hLog : ∃ L : ℂ → ℂ,
        AnalyticOnNhd ℂ L rightHalfPlane ∧
        EqOn (Complex.exp ∘ L) shiftedXi rightHalfPlane) :
      criticalLineHypothesis := by
    obtain ⟨L, _, hLExp⟩ := hLog
    have noRightXiZero : ∀ s : ℂ,
        (1 : ℝ) / 2 < s.re → xiReading s ≠ 0 := by
      intro s hs hXi
      let z : ℂ := s - (1 / 2 : ℂ)
      have hz : z ∈ rightHalfPlane := by
        change 0 < z.re
        norm_num [z]
        linarith
      have hValue := hLExp hz
      have hShift : (1 / 2 : ℂ) + z = s := by
        dsimp only [z]
        ring
      change Complex.exp (L z) = xiReading ((1 / 2 : ℂ) + z) at hValue
      rw [hShift, hXi] at hValue
      exact Complex.exp_ne_zero _ hValue
    intro s hNontrivial
    have hsZero : s ≠ 0 := by
      intro hs
      subst s
      norm_num [IsNontrivialZero] at hNontrivial
    have hsOne : s ≠ 1 := by
      intro hs
      subst s
      norm_num [IsNontrivialZero] at hNontrivial
    have hCompleted : completedRiemannZeta s = 0 :=
      completedRiemannZeta_eq_zero_iff.mpr hNontrivial
    have hCompletedReading : completedZetaReading s = 0 := by
      simpa only [completedZetaReading] using hCompleted
    have hXi : xiReading s = 0 := by
      rw [xi_reading_eq_completed_zeta hsZero hsOne, hCompletedReading]
      simp
    by_cases hRight : (1 : ℝ) / 2 < s.re
    · exact False.elim (noRightXiZero s hRight hXi)
    by_cases hLine : s.re = (1 : ℝ) / 2
    · exact hLine
    have hLeft : s.re < (1 : ℝ) / 2 := lt_of_le_of_ne
      (le_of_not_gt hRight) hLine
    have hReflectedXi : xiReading (1 - s) = 0 := by
      rw [xi_reading_reflection, hXi]
    have hReflectedRight : (1 : ℝ) / 2 < (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    exact False.elim (noRightXiZero (1 - s) hReflectedRight hReflectedXi)
  have globalLogOfCritical (hCritical : criticalLineHypothesis) :
      ∃ L : ℂ → ℂ,
        AnalyticOnNhd ℂ L rightHalfPlane ∧
        EqOn (Complex.exp ∘ L) shiftedXi rightHalfPlane :=
    exists_analytic_log_on_open_convex hOpen hConvex hNonempty hAnalytic
      (xiNonzeroOfCritical hCritical)
  refine ⟨⟨globalLogOfCritical, criticalOfGlobalLog⟩, ?_, ?_⟩
  · intro hCritical
    obtain ⟨L, hLAnalytic, hLExp⟩ := globalLogOfCritical hCritical
    exact ⟨L, hLAnalytic, hLExp, phase_gauge_continuous hOpen hLAnalytic⟩
  · intro z₀ hz₀ hZero
    constructor
    · rintro ⟨L, _, hLExp⟩
      have hValue := hLExp hz₀
      rw [hZero] at hValue
      exact Complex.exp_ne_zero _ hValue
    · intro domain L hExp hz₀Domain
      have hValue := hExp hz₀Domain
      rw [hZero] at hValue
      exact Complex.exp_ne_zero _ hValue

#print axioms global_logarithmic_gauge_criterion

end D5.S3.Analytic.Adelic.GlobalLogarithmicGaugeCriterion
