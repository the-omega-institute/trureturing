/- GID: D5/S3/Analytic/Laplace/PositiveEulerContinuation
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/PositiveEulerContinuation
   mirror-E: none(waiver:analytic-proof-only)
   anchors: [mathlib/module/Mathlib.Analysis.Meromorphic.Order]
   utility: none
   digest: Real-regular meromorphic Euler forcing forces positive Laplace convergence. -/

import D5.S3.Analytic.Laplace.AbscissaSingularity
import D5.S3.Analytic.Laplace.EulerLocalContinuation
import Mathlib.Analysis.Meromorphic.Order

/-! The convergence boundary is derived from the actual exponential integrals.
A zero meromorphic Euler defect propagates as a germ; pointwise equality is
recovered only where the forcing and the actual transform are holomorphic. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology

namespace D5.S3.Analytic.Laplace.PositiveEulerContinuation

open AbscissaSingularity EulerLocalContinuation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

private theorem convergence_upper (hXm : AEMeasurable X μ)
    (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω) {s t : ℝ}
    (hs : s ∈ convergenceSet X μ) (hst : s ≤ t) : t ∈ convergenceSet X μ := by
  apply hs.mono'
  · have hm : AEMeasurable (fun ω => Real.exp (-t * X ω)) μ := by fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [hX] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hst) hω)

private theorem analytic_laplace {c : ℝ} (h : Ioi c ⊆ convergenceSet X μ) :
    AnalyticOnNhd ℂ (fun z => complexMGF X μ (-z)) {z | c < z.re} := by
  have hreflect : Iio (-c) ⊆ integrableExpSet X μ := by
    intro u hu
    have hi := h (show -u ∈ Ioi c by change c < -u; change u < -c at hu; linarith)
    simpa only [convergenceSet, mem_ofPred_eq, integrableExpSet, neg_neg] using hi
  intro z hz
  change c < z.re at hz
  have hi : (-z).re ∈ interior (integrableExpSet X μ) := by
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (isOpen_Iio.mem_nhds (show (-z).re ∈ Iio (-c) by
      simp only [mem_Iio, neg_re]; linarith)) hreflect
  exact (analyticAt_complexMGF hi).comp (analyticAt_id.neg)

private theorem laplace_zero_limit [IsFiniteMeasure μ]
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω) :
    Tendsto (fun x : ℝ => complexMGF X μ (-(x : ℂ))) (𝓝[Ioi 0] 0)
      (𝓝 (∫ _ : Ω, (1 : ℂ) ∂μ)) := by
  have hm : ∀ᶠ x : ℝ in 𝓝[Ioi 0] 0,
      AEStronglyMeasurable (fun ω => Complex.exp (-(x : ℂ) * X ω)) μ := by
    exact Eventually.of_forall (fun x => by fun_prop)
  have hb : ∀ᶠ x : ℝ in 𝓝[Ioi 0] 0,
      ∀ᵐ ω ∂μ, ‖Complex.exp (-(x : ℂ) * X ω)‖ ≤ (1 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    filter_upwards [hX] with ω hω
    rw [Complex.norm_exp]
    simp only [mul_re, neg_re, ofReal_re, ofReal_im, neg_im, mul_zero, sub_zero]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx.le) hω)
  have hl : ∀ᵐ ω ∂μ, Tendsto (fun x : ℝ => Complex.exp (-(x : ℂ) * X ω))
      (𝓝[Ioi 0] 0) (𝓝 (1 : ℂ)) := by
    apply Eventually.of_forall
    intro ω
    have hx : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[Ioi 0] 0) (𝓝 (0 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa [Function.comp_def] using (Complex.continuous_exp.tendsto (-(0 : ℂ) * (X ω : ℂ))).comp
      (hx.neg.mul_const (X ω : ℂ))
  exact tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    hm hb (integrable_const 1) hl

/-- Actual exponential integrability on the entire forcing half-plane follows
from the Euler equation on the positive half-plane, with no continuation or
moment-growth hypothesis. -/
theorem integrable_and_analytic_of_euler [IsFiniteMeasure μ]
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    {a : ℝ} (ha : a < 0) {R : ℂ → ℂ}
    (hRm : MeromorphicOn R {z | a < z.re})
    (hRa : ∀ x : ℝ, a < x → AnalyticAt ℂ R (x : ℂ))
    (hode : ∀ z : ℂ, 0 < z.re →
      z * deriv (deriv (fun w => complexMGF X μ (-w))) z +
        2 * deriv (fun w => complexMGF X μ (-w)) z = R z) :
    (∀ x : ℝ, a < x → Integrable (fun ω => Real.exp (-x * X ω)) μ) ∧
      AnalyticOnNhd ℂ (fun z => complexMGF X μ (-z)) {z | a < z.re} := by
  have hzero : (0 : ℝ) ∈ convergenceSet X μ := by
    simp [convergenceSet]
  have hconv : ∀ x : ℝ, a < x → x ∈ convergenceSet X μ := by
    intro x hax
    by_contra hx
    have hne : (convergenceSet X μ).Nonempty := ⟨0, hzero⟩
    have hbound : ∀ s ∈ convergenceSet X μ, x ≤ s := by
      intro s hs
      by_contra hxs
      exact hx (convergence_upper hXm hX hs (le_of_lt (lt_of_not_ge hxs)))
    have hbdd : BddBelow (convergenceSet X μ) := ⟨x, hbound⟩
    let σ : ℝ := sInf (convergenceSet X μ)
    have hxσ : x ≤ σ := le_csInf hne hbound
    have hσ0 : σ ≤ 0 := csInf_le hbdd hzero
    have haσ : a < σ := lt_of_lt_of_le hax hxσ
    have hright : Ioi σ ⊆ convergenceSet X μ := by
      intro t ht
      obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt hne ht
      exact convergence_upper hXm hX hs hst.le
    let G : ℂ → ℂ := fun z => complexMGF X μ (-z)
    let U : Set ℂ := {z | σ < z.re}
    have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hUc : IsPreconnected U := (convex_halfSpace_re_gt σ).isPreconnected
    have hGa : AnalyticOnNhd ℂ G U := analytic_laplace hright
    let D : ℂ → ℂ := fun z => z * deriv (deriv G) z + 2 * deriv G z - R z
    have hDm : MeromorphicOn D U := by
      have hGm := hGa.meromorphicOn
      have hR' : MeromorphicOn R U := fun z hz => hRm z (lt_trans haσ hz)
      exact ((analyticOnNhd_id.meromorphicOn.mul hGm.deriv.deriv).add
        ((analyticOnNhd_const.meromorphicOn).mul hGm.deriv)).sub hR'
    have hD1 : meromorphicOrderAt D (1 : ℂ) = ⊤ := by
      apply meromorphicOrderAt_eq_top_iff.mpr
      apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with z hz
      exact sub_eq_zero.mpr (hode z hz)
    have hDtop : ∀ z ∈ U, meromorphicOrderAt D z = ⊤ := by
      intro z hz
      exact hDm.meromorphicOrderAt_eq_top_of_isPreconnected hUc
        (show (1 : ℂ) ∈ U by change σ < (1 : ℂ).re; simp only [one_re]; linarith) hz hD1
    obtain ⟨r, hr, hrR⟩ := Metric.mem_nhds_iff.mp (hRa σ haσ).eventually_analyticAt
    have hRball : DifferentiableOn ℂ R (Metric.ball (σ : ℂ) r) :=
      fun z hz => (hrR hz).differentiableAt.differentiableWithinAt
    have hGd : DifferentiableOn ℂ G U := hGa.differentiableOn
    have hGd1 : DifferentiableOn ℂ (deriv G) U := hGd.deriv hU
    have hGd2 : DifferentiableOn ℂ (deriv (deriv G)) U := hGd1.deriv hU
    have hF : DifferentiableOn ℂ G (rightHalfDisk σ r) := hGd.mono (fun _ hz => hz.2)
    have hODE : ∀ z ∈ rightHalfDisk σ r,
        z * deriv (deriv G) z + 2 * deriv G z = R z := by
      intro z hz
      have hDc : ContinuousAt D z :=
        ((continuousAt_id.mul (hGd2.differentiableAt (hU.mem_nhds hz.2)).continuousAt).add
          ((hGd1.differentiableAt (hU.mem_nhds hz.2)).continuousAt.const_mul 2)).sub
            (hRball.differentiableAt (Metric.isOpen_ball.mem_nhds hz.1)).continuousAt
      have hp : D =ᶠ[𝓝[≠] z] (fun _ => 0) :=
        meromorphicOrderAt_eq_top_iff.mp (hDtop z hz.2)
      have hDz : D z = 0 := tendsto_nhds_unique
        (hDc.tendsto.mono_left nhdsWithin_le_nhds) (tendsto_const_nhds.congr' hp.symm)
      exact sub_eq_zero.mp hDz
    have hext : ∃ δ : ℝ, 0 < δ ∧ ∃ H : ℂ → ℂ,
        DifferentiableOn ℂ H (Metric.ball (σ : ℂ) δ) ∧
          EqOn H G (rightHalfDisk σ δ) := by
      by_cases hs : σ = 0
      · have hlim := laplace_zero_limit hXm hX
        rw [hs] at hRball hF hODE ⊢
        obtain ⟨δ, hδ, _, H, hH, heq, _⟩ :=
          exists_extension_at_zero hr hRball hF hODE hlim
        exact ⟨δ, hδ, H, hH, heq⟩
      · obtain ⟨δ, hδ, _, H, hH, heq⟩ := exists_extension_of_ne_zero hs hr hRball hF hODE
        exact ⟨δ, hδ, H, hH, heq⟩
    obtain ⟨δ, hδ, H, hH, heq⟩ := hext
    exact no_holomorphic_extension_at_abscissa hXm hX hne hbdd hδ
      ⟨hH, fun z hz hzr => heq ⟨hz, hzr⟩⟩
  exact ⟨hconv, analytic_laplace (fun _ hx => hconv _ hx)⟩

end D5.S3.Analytic.Laplace.PositiveEulerContinuation
