/- GID: D5/S3/Analytic/SincSquareDerivativeBudget
   generality: G
   mirror-B: D5/B/S3/Analytic/SincSquareDerivativeBudget
   mirror-E: none(waiver:unbounded-symbolic-derivative-estimate)
   anchors: []
   utility: none
   digest: Positive integral recurrences control all derivatives of the entire cosine square-root function. -/

import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open MeasureTheory Set Filter
open scoped Topology Nat

namespace SincSquareDerivativeBudget

/-- The entire extension of `cos (sqrt t)`, defined by its everywhere convergent series. -/
noncomputable def psi : ℝ → ℝ :=
  FormalMultilinearSeries.ofScalarsSum (fun k => (-1 : ℝ) ^ k / (2 * k)!)

private theorem psi_radius :
    (FormalMultilinearSeries.ofScalars ℝ (fun k => (-1 : ℝ) ^ k / (2 * k)!)).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  convert (Real.hasSum_cosh (Real.sqrt r)).summable using 1
  ext k
  rw [FormalMultilinearSeries.ofScalars_norm]
  simp only [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_natCast,
    one_div, mul_comm _ ((r : ℝ) ^ k)]
  rw [show 2 * k = 2 * k from rfl, pow_mul, Real.sq_sqrt r.coe_nonneg]
  rfl

private theorem psi_smooth : ContDiff ℝ ⊤ psi := by
  apply AnalyticOnNhd.contDiff
  intro t _
  apply (FormalMultilinearSeries.analyticOnNhd _)
  simp [psi_radius, Metric.eball_top]

private theorem psi_eq_cos {t : ℝ} (ht : 0 ≤ t) : psi t = Real.cos (Real.sqrt t) := by
  rw [psi, FormalMultilinearSeries.ofScalars_sum_eq, Real.cos_eq_tsum]
  apply tsum_congr
  intro k
  simp only [smul_eq_mul, pow_mul, Real.sq_sqrt ht]
  ring

private theorem psi_zero : psi 0 = 1 := by
  simp [psi, FormalMultilinearSeries.ofScalarsSum_zero]

end SincSquareDerivativeBudget
