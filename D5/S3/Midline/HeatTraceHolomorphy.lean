/- GID: D5/S3/Midline/HeatTraceHolomorphy
   generality: G
   mirror-B: D5/B/S3/Midline/HeatTraceHolomorphy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.LocallyUniformLimit]
   digest: The heat trace is analytic throughout its convergence half-plane. -/

import D5.S3.Midline.UniversalHeatTrace
import Mathlib.Analysis.Complex.LocallyUniformLimit

/- Provenance: Native proof over pinned mathlib and frozen repository results. -/

namespace D5.S3.Midline.HeatTraceHolomorphy

open D5.S3.Midline.UniversalHeatTrace

variable {A : Type*} [Countable A] [Zero A]

omit [Countable A] [Zero A] in
/-- A heat trace is analytic at every point strictly to the right of its heat abscissa. -/
theorem heat_trace_analyticOnNhd_of_abscissa
    (M : A → ℝ) (α : ℝ) (hMnn : ∀ a, 0 ≤ M a)
    (hAbscissa : IsHeatAbscissa M α) :
    AnalyticOnNhd ℂ (heatTrace M) {s : ℂ | α < s.re} := by
  apply DifferentiableOn.analyticOnNhd ?_
    (isOpen_lt continuous_const Complex.continuous_re)
  intro s₀ hs₀
  let σ := (α + s₀.re) / 2
  have hασ : α < σ := by
    change α < s₀.re at hs₀
    dsimp [σ]
    linarith
  have hσs₀ : σ < s₀.re := by
    change α < s₀.re at hs₀
    dsimp [σ]
    linarith
  let U : Set ℂ := {s | σ < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hs₀U : s₀ ∈ U := hσs₀
  have hsum : Summable (fun a => Real.exp (-σ * M a)) :=
    hAbscissa.1 σ hασ
  have hterm (a : A) :
      DifferentiableOn ℂ (fun s : ℂ => heatCoefficient M s a) U := by
    change DifferentiableOn ℂ (fun s : ℂ => Complex.exp (-s * (M a : ℂ))) U
    exact (Complex.differentiable_exp.comp
      (differentiable_id.neg.mul_const (M a : ℂ))).differentiableOn
  have hbound (a : A) (s : ℂ) (hs : s ∈ U) :
      ‖heatCoefficient M s a‖ ≤ Real.exp (-σ * M a) := by
    rw [heatCoefficient_norm]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (le_of_lt hs)) (hMnn a)
  have hdiff : DifferentiableOn ℂ (heatTrace M) U :=
    Complex.differentiableOn_tsum_of_summable_norm hsum hterm hU hbound
  exact (hdiff.differentiableAt (hU.mem_nhds hs₀U)).differentiableWithinAt

omit [Countable A] [Zero A] in
example (M : A → ℝ) (α : ℝ) (hMnn : ∀ a, 0 ≤ M a)
    (hAbscissa : IsHeatAbscissa M α) :
    AnalyticOnNhd ℂ (heatTrace M) {s : ℂ | α < s.re} :=
  heat_trace_analyticOnNhd_of_abscissa M α hMnn hAbscissa

end D5.S3.Midline.HeatTraceHolomorphy
