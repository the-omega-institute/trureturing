import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Omega original.

The first and mixed derivatives of the elementary half-integer radial profile
after canceling its spacelike scaling factor.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega.HalfIntegerBesselRadial

def radialScale (y : ℝ) : ℝ := 1 / (8 * Real.pi ^ 2 * y * Real.sqrt y)

def scaledProfile (M y u v : ℝ) : ℝ :=
  let z := M * Real.sqrt (u * v * y)
  radialScale y * (Real.exp (-z) * (1 + z) - 1)

private theorem sqrtLinear_hasDerivAt {m a b t : ℝ} (ht : 0 < a * t * b) :
    HasDerivAt (fun s : ℝ => m * Real.sqrt (a * s * b))
      (m * ((a * b) / (2 * Real.sqrt (a * t * b)))) t := by
  have h := (((hasDerivAt_id t).const_mul a).mul_const b).sqrt ht.ne'
  convert h.const_mul m using 1 <;> simp

theorem firstRadialDerivative (M : ℝ) {u v y : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hy : 0 < y) : HasDerivAt (scaledProfile M y u)
      (radialScale y * (-(M ^ 2 * u * y / 2) * Real.exp (-M * Real.sqrt (u * v * y)))) v := by
  have hq : 0 < u * v * y := by positivity
  have hz := sqrtLinear_hasDerivAt (m := M) hq
  have h := ((hz.neg.exp.mul (hz.const_add 1)).sub_const 1).const_mul (radialScale y)
  convert h using 1
  · rfl
  · simp only [Pi.neg_apply, neg_mul]
    field_simp [(Real.sqrt_pos.mpr hq).ne']
    ring

theorem secondRadialDerivative (M : ℝ) {u v y : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hy : 0 < y) :
    HasDerivAt (fun s : ℝ =>
      radialScale y * (-(M ^ 2 * s * y / 2) * Real.exp (-M * Real.sqrt (s * v * y))))
      ((M ^ 2 / (32 * Real.pi ^ 2 * Real.sqrt y)) * Real.exp (-(M * Real.sqrt (u * v * y))) *
        (M * Real.sqrt (u * v * y) - 2)) u := by
  have hq : 0 < v * u * y := by positivity
  have hz := sqrtLinear_hasDerivAt (m := M) hq
  have hlin := ((((hasDerivAt_id u).const_mul (M ^ 2)).mul_const y).div_const 2).neg
  have h := (hlin.mul hz.neg.exp).const_mul (radialScale y)
  have heq : (fun s : ℝ => M * Real.sqrt (v * s * y)) =
      (fun s : ℝ => M * Real.sqrt (s * v * y)) := by
    funext s
    rw [mul_comm v s]
  rw [heq] at h
  convert h using 1
  · simp only [Pi.neg_apply, Pi.mul_apply, id_eq, neg_mul]
  · simp only [radialScale, Pi.neg_apply, id_eq, mul_one, neg_mul]
    rw [mul_comm v u]
    have hs := Real.sq_sqrt (mul_pos (mul_pos hu hv) hy).le
    have hs₀ := (Real.sqrt_pos.mpr (mul_pos (mul_pos hu hv) hy)).ne'
    field_simp [Real.pi_ne_zero, hy.ne', (Real.sqrt_pos.mpr hy).ne', hs₀]
    linear_combination 32 * M ^ 3 * hs

end Omega.HalfIntegerBesselRadial
