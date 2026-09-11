/- GID: D5/S3/Analytic/Interpolation/LogOneSubExpDerivatives
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/LogOneSubExpDerivatives
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The logarithm of one minus a negative exponential has a positive third derivative on the positive half-line. -/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open Set Filter
open scoped Topology

namespace D5.S3.Analytic.Interpolation.LogOneSubExpDerivatives

private theorem first_derivative {x : ℝ} (hx : 0 < x) :
    deriv (fun t : ℝ => Real.log (1 - Real.exp (-t))) x = 1 / (Real.exp x - 1) := by
  have he : Real.exp (-x) < 1 := by simpa using Real.exp_lt_exp.mpr (neg_neg_of_pos hx)
  have hp : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)
  have hd := ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).neg.exp)).log
    (ne_of_gt (sub_pos.mpr he))
  simp only [Pi.sub_apply, Pi.neg_apply, id_eq] at hd
  rw [hd.deriv]
  simp only [mul_neg_one, sub_neg_eq_add, zero_add]
  apply (div_eq_div_iff (ne_of_gt (sub_pos.mpr he)) hp.ne').mpr
  rw [mul_sub, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, one_mul]

private theorem second_derivative {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 (fun t : ℝ => Real.log (1 - Real.exp (-t))) x =
      -Real.exp x / (Real.exp x - 1)^2 := by
  have he : Real.exp x - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)).ne'
  have hlocal : deriv (fun t : ℝ => Real.log (1 - Real.exp (-t))) =ᶠ[𝓝 x]
      (fun t : ℝ => 1 / (Real.exp t - 1)) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact first_derivative ht
  rw [show (2 : ℕ) = 1 + 1 by decide, iteratedDeriv_succ, iteratedDeriv_one,
    hlocal.deriv_eq]
  have hd := (hasDerivAt_const x (1 : ℝ)).div
    ((Real.hasDerivAt_exp x).sub_const 1) he
  simpa [Pi.div_def] using hd.deriv

private theorem third_derivative {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 3 (fun t : ℝ => Real.log (1 - Real.exp (-t))) x =
      Real.exp x * (Real.exp x + 1) / (Real.exp x - 1)^3 := by
  have he : Real.exp x - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)).ne'
  have hlocal : iteratedDeriv 2 (fun t : ℝ => Real.log (1 - Real.exp (-t))) =ᶠ[𝓝 x]
      (fun t : ℝ => -Real.exp t / (Real.exp t - 1)^2) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact second_derivative ht
  rw [show (3 : ℕ) = 2 + 1 by decide, iteratedDeriv_succ, hlocal.deriv_eq]
  have hd := (Real.hasDerivAt_exp x).neg.div
    (((Real.hasDerivAt_exp x).sub_const 1).pow 2) (pow_ne_zero 2 he)
  simp only [Pi.div_def, Pi.neg_def, Pi.pow_def] at hd
  rw [hd.deriv]
  field_simp [he]
  ring

/-- Smoothness and the first three derivatives on the positive half-line. -/
theorem log_one_sub_exp_derivatives :
    ContDiffOn ℝ 3 (fun t : ℝ => Real.log (1 - Real.exp (-t))) (Ioi 0) ∧
    ∀ x : ℝ, 0 < x →
      deriv (fun t : ℝ => Real.log (1 - Real.exp (-t))) x = 1 / (Real.exp x - 1) ∧
      iteratedDeriv 2 (fun t : ℝ => Real.log (1 - Real.exp (-t))) x =
        -Real.exp x / (Real.exp x - 1)^2 ∧
      iteratedDeriv 3 (fun t : ℝ => Real.log (1 - Real.exp (-t))) x =
        Real.exp x * (Real.exp x + 1) / (Real.exp x - 1)^3 ∧
      0 < iteratedDeriv 3 (fun t : ℝ => Real.log (1 - Real.exp (-t))) x := by
  constructor
  · apply (contDiffOn_const.sub (contDiffOn_id.neg.exp)).log
    intro x hx
    have he : Real.exp (-x) < 1 := by
      simpa using Real.exp_lt_exp.mpr (neg_neg_of_pos hx)
    exact (sub_pos.mpr he).ne'
  · intro x hx
    refine ⟨first_derivative hx, second_derivative hx, third_derivative hx, ?_⟩
    rw [third_derivative hx]
    exact div_pos (mul_pos (Real.exp_pos _) (by positivity))
      (pow_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)) 3)

end D5.S3.Analytic.Interpolation.LogOneSubExpDerivatives
