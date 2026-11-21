/- GID: D5/S3/Analytic/Laplace/PositiveLaplaceContinuation
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/PositiveLaplaceContinuation
   mirror-E: none(waiver:analytic-proof-only)
   anchors: [mathlib/module/Mathlib.Analysis.Meromorphic.Order]
   utility: none
   digest: A real-regular meromorphic continuation forces positive Laplace convergence. -/

import D5.S3.Analytic.Laplace.PositiveEulerContinuation

/-! Extension of a positive Laplace integral across a real-regular meromorphic corridor. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology

namespace D5.S3.Analytic.Laplace.PositiveLaplaceContinuation

open AbscissaSingularity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- An initially convergent positive Laplace transform converges throughout a
meromorphic continuation half-plane if the continuation is analytic at all real
points where the convergence boundary could lie. Agreement near one point to
the right of both thresholds determines the continuation as a meromorphic germ
throughout the half-plane and determines its value at every point of continuity. -/
theorem integrable_and_analytic_of_meromorphic_continuation
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    {a b : ℝ} (hb : Integrable (fun ω => Real.exp (-b * X ω)) μ)
    {H : ℂ → ℂ} (hHm : MeromorphicOn H {z | a < z.re})
    (hHa : ∀ x : ℝ, a < x → x ≤ b → AnalyticAt ℂ H (x : ℂ))
    {z₀ : ℂ} (ha₀ : a < z₀.re) (hb₀ : b < z₀.re)
    (hAgree : H =ᶠ[𝓝 z₀] fun z => complexMGF X μ (-z)) :
    (∀ x : ℝ, a < x → Integrable (fun ω => Real.exp (-x * X ω)) μ) ∧
    AnalyticOnNhd ℂ (fun z => complexMGF X μ (-z)) {z | a < z.re} ∧
    ∀ z : ℂ, a < z.re →
      Integrable (fun ω => Complex.exp (-z * (X ω : ℂ))) μ ∧
      (H =ᶠ[𝓝[≠] z] fun w => complexMGF X μ (-w)) ∧
      (ContinuousAt H z → H z = complexMGF X μ (-z)) := by
  let L : ℂ → ℂ := fun z => complexMGF X μ (-z)
  let D : ℂ → ℂ := fun z => H z - L z
  have hD₀ : meromorphicOrderAt D z₀ = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [hAgree.filter_mono nhdsWithin_le_nhds] with z hz
    exact sub_eq_zero.mpr hz
  have hGerm {c : ℝ} (hac : a ≤ c) (hc₀ : c < z₀.re)
      (hL : AnalyticOnNhd ℂ L {z | c < z.re}) {z : ℂ} (hz : c < z.re) :
      H =ᶠ[𝓝[≠] z] L := by
    have hHm' : MeromorphicOn H {w : ℂ | c < w.re} :=
      fun w hw => hHm w (hac.trans_lt hw)
    have hDm : MeromorphicOn D {w | c < w.re} := hHm'.sub hL.meromorphicOn
    have hTop := hDm.meromorphicOrderAt_eq_top_of_isPreconnected
      (convex_halfSpace_re_gt c).isPreconnected hc₀ hz hD₀
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp hTop] with w hw
    exact sub_eq_zero.mp hw
  have hValue {z : ℂ} (h : H =ᶠ[𝓝[≠] z] L) (hH : ContinuousAt H z)
      (hL : ContinuousAt L z) : H z = L z :=
    tendsto_nhds_unique (hH.tendsto.mono_left nhdsWithin_le_nhds)
      ((hL.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)
  have hUpper {s t : ℝ} (hs : s ∈ convergenceSet X μ) (hst : s ≤ t) :
      t ∈ convergenceSet X μ := by
    apply hs.mono'
    · have hm : AEMeasurable (fun ω => Real.exp (-t * X ω)) μ := by fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards [hX] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hst) hω)
  have hConv : ∀ x : ℝ, a < x → x ∈ convergenceSet X μ := by
    intro x hax
    by_contra hx
    have hne : (convergenceSet X μ).Nonempty := ⟨b, hb⟩
    have hbound : ∀ s ∈ convergenceSet X μ, x ≤ s := by
      intro s hs
      by_contra hxs
      exact hx (hUpper hs (le_of_lt (lt_of_not_ge hxs)))
    have hbdd : BddBelow (convergenceSet X μ) := ⟨x, hbound⟩
    let σ := sInf (convergenceSet X μ)
    have haσ : a < σ := hax.trans_le (le_csInf hne hbound)
    have hσb : σ ≤ b := csInf_le hbdd hb
    have hright : Ioi σ ⊆ convergenceSet X μ := by
      intro t ht
      obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt hne ht
      exact hUpper hs hst.le
    have hL : AnalyticOnNhd ℂ L {z | σ < z.re} :=
      PositiveEulerContinuation.analytic_laplace hright
    obtain ⟨r, hr, hrH⟩ := Metric.mem_nhds_iff.mp (hHa σ haσ hσb).eventually_analyticAt
    have hEq : EqOn H L (Metric.ball (σ : ℂ) r ∩ {z | σ < z.re}) := by
      intro z hz
      exact hValue (hGerm haσ.le (hσb.trans_lt hb₀) hL hz.2)
        (hrH hz.1).continuousAt (hL z hz.2).continuousAt
    exact no_holomorphic_extension_at_abscissa hXm hX hne hbdd hr
      ⟨fun z hz => (hrH hz).differentiableAt.differentiableWithinAt,
        fun z hz hzr => hEq ⟨hz, hzr⟩⟩
  have hL : AnalyticOnNhd ℂ L {z | a < z.re} :=
    PositiveEulerContinuation.analytic_laplace (fun _ hx => hConv _ hx)
  refine ⟨hConv, hL, fun z hz => ?_⟩
  have hi : Integrable (fun ω => Complex.exp (-z * (X ω : ℂ))) μ := by
    have hm : AEStronglyMeasurable (fun ω => Complex.exp (-z * (X ω : ℂ))) μ := by
      fun_prop
    apply (integrable_norm_iff hm).mp
    simpa only [Complex.norm_exp, mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      using (show Integrable (fun ω => Real.exp (-z.re * X ω)) μ from hConv z.re hz)
  have h := hGerm le_rfl ha₀ hL hz
  exact ⟨hi, h, fun hH => hValue h hH (hL z hz).continuousAt⟩

#print axioms integrable_and_analytic_of_meromorphic_continuation

end D5.S3.Analytic.Laplace.PositiveLaplaceContinuation
