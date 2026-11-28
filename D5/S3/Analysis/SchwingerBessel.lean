/- GID: D5/S3/Analysis/SchwingerBessel
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-schwinger4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The first positive order of the hyperbolic cosine integral is obtained by averaging the two equivalent Schwinger integrands before logarithmic substitution. -/

import D5.S3.Analysis.SchwingerIntegral
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
Omega original.

The first positive order of the hyperbolic cosine integral is obtained by
averaging the two equivalent Schwinger integrands before logarithmic
substitution. The resulting integrand is even.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace Omega

/-- The Schwinger integral in the hyperbolic cosine representation of order one. -/
theorem schwingerIntegral_eq_cosh_integral {t : ℝ} (ht : 0 < t) :
    schwingerIntegral t =
      (2 * Real.sqrt t) * ∫ s in Ioi (0 : ℝ),
        Real.exp (-(2 * Real.sqrt t) * Real.cosh s) * Real.cosh s := by
  let g (s : ℝ) := (Real.exp (-s - t / s) + t * (s⁻¹ ^ 2 * Real.exp (-s - t / s))) / 2
  have havg : schwingerIntegral t = ∫ s in Ioi (0 : ℝ), g s := by
    have hi : IntegrableOn (fun s : ℝ => Real.exp (-s - t / s)) (Ioi 0) := by
      simpa using schwingerMoment_integrable 0 ht
    simp only [g, integral_div, integral_add hi ((schwingerMoment_integrable 2 ht).const_mul t),
      integral_const_mul]
    change schwingerIntegral t = (schwingerIntegral t + t * schwingerMoment 2 t) / 2
    rw [← schwingerIntegral_eq_mul_moment_two ht]
    ring
  rw [havg, ← integral_comp_exp]
  rw [← integral_add_right_eq_self (fun s : ℝ => Real.exp s • g (Real.exp s))
    (Real.log (Real.sqrt t))]
  have hr : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hchange (s : ℝ) :
      Real.exp (s + Real.log (Real.sqrt t)) • g (Real.exp (s + Real.log (Real.sqrt t))) =
        Real.sqrt t * (Real.exp (-(2 * Real.sqrt t) * Real.cosh s) * Real.cosh s) := by
    dsimp only [g]
    rw [Real.exp_add, Real.exp_log hr, smul_eq_mul, Real.cosh_eq, Real.exp_neg]
    generalize Real.sqrt t = r at hr hsq ⊢
    have he : -(Real.exp s * r) - t / (Real.exp s * r) =
        -(2 * r) * ((Real.exp s + (Real.exp s)⁻¹) / 2) := by
      rw [← hsq]
      field_simp [hr.ne', (Real.exp_pos s).ne']
      ring
    rw [he, ← hsq]
    field_simp [hr.ne', (Real.exp_pos s).ne']
  simp_rw [hchange]
  rw [integral_const_mul]
  have heven :
      (fun s : ℝ => Real.exp (-(2 * Real.sqrt t) * Real.cosh |s|) * Real.cosh |s|) =
        (fun s : ℝ => Real.exp (-(2 * Real.sqrt t) * Real.cosh s) * Real.cosh s) := by
    funext s
    rw [Real.cosh_abs]
  conv_lhs => rw [← heven]
  rw [integral_comp_abs (f := fun s : ℝ =>
    Real.exp (-(2 * Real.sqrt t) * Real.cosh s) * Real.cosh s)]
  ring

end Omega
