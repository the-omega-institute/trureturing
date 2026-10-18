/- GID: D5/S3/Arith/Robin/LogLogHigherDerivative
   generality: G
   mirror-B: none(waiver:analytic-kernel)
   mirror-E: none(waiver:analytic-kernel)
   anchors: []
   utility: none
   digest: Positive-order log-log derivatives have strict alternating signs on x > 1. -/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/- The recursive kernel expands successive derivatives of inverse powers of x
   and log x into terms with positive coefficients. Differentiation negates the
   next kernel, giving every positive-order derivative of log(log(x)) on x > 1.
   Transport to mixed arithmetic corner differences requires repeated FTC and
   cancellation of the distinct-prime local divisor terms; it is not asserted
   here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.LogLogHigherDerivative

open Filter Set
open scoped Topology

/-- A positive expansion of successive derivatives of inverse powers of x and log x. -/
def positiveKernel : ℕ → ℕ → ℕ → ℝ → ℝ
  | 0, a, b, x => x⁻¹ ^ (a + 1) * (Real.log x)⁻¹ ^ (b + 1)
  | m + 1, a, b, x =>
      (a + 1 : ℝ) * positiveKernel m (a + 1) b x +
        (b + 1 : ℝ) * positiveKernel m (a + 1) (b + 1) x

theorem positiveKernel_pos (m a b : ℕ) {x : ℝ} (hx : 1 < x) :
    0 < positiveKernel m a b x := by
  induction m generalizing a b with
  | zero =>
      unfold positiveKernel
      exact mul_pos (pow_pos (inv_pos.mpr (by linarith)) _)
        (pow_pos (inv_pos.mpr (Real.log_pos hx)) _)
  | succ m ih =>
      unfold positiveKernel
      exact add_pos (mul_pos (by positivity) (ih (a + 1) b))
        (mul_pos (by positivity) (ih (a + 1) (b + 1)))

private theorem hasDerivAt_positiveKernel (m a b : ℕ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (positiveKernel m a b) (-positiveKernel (m + 1) a b x) x := by
  induction m generalizing a b with
  | zero =>
      have hx0 : x ≠ 0 := ne_of_gt (by linarith)
      have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
      have hi := (hasDerivAt_id x).inv hx0
      have hl := (Real.hasDerivAt_log hx0).inv hl0
      change HasDerivAt
        (fun y : ℝ => y⁻¹ ^ (a + 1) * (Real.log y)⁻¹ ^ (b + 1)) _ x
      apply ((hi.pow (a + 1)).mul (hl.pow (b + 1))).congr_deriv
      simp only [positiveKernel, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
        id_eq, Pi.pow_apply, Pi.inv_apply, pow_succ]
      field_simp
      ring
  | succ m ih =>
      change HasDerivAt
        (fun y => (a + 1 : ℝ) * positiveKernel m (a + 1) b y +
          (b + 1 : ℝ) * positiveKernel m (a + 1) (b + 1) y) _ x
      apply (((ih (a + 1) b).const_mul (a + 1 : ℝ)).add
        ((ih (a + 1) (b + 1)).const_mul (b + 1 : ℝ))).congr_deriv
      simp only [positiveKernel]
      ring

private theorem iteratedDeriv_logLog_eq (m : ℕ) {x : ℝ} (hx : 1 < x) :
    iteratedDeriv (m + 1) (fun y : ℝ => Real.log (Real.log y)) x =
      (-1 : ℝ) ^ m * positiveKernel m 0 0 x := by
  induction m generalizing x with
  | zero =>
      rw [iteratedDeriv_succ]
      simp only [iteratedDeriv_zero, pow_zero, one_mul]
      have hd := (Real.hasDerivAt_log (ne_of_gt (by linarith : 0 < x))).log
        (Real.log_pos hx).ne'
      simpa [positiveKernel, div_eq_mul_inv] using hd.deriv
  | succ m ih =>
      rw [iteratedDeriv_succ]
      have hevent :
          iteratedDeriv (m + 1) (fun y : ℝ => Real.log (Real.log y)) =ᶠ[𝓝 x]
            fun y => (-1 : ℝ) ^ m * positiveKernel m 0 0 y := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact ih hy
      rw [hevent.deriv_eq]
      rw [((hasDerivAt_positiveKernel m 0 0 hx).const_mul ((-1 : ℝ) ^ m)).deriv]
      rw [pow_succ]
      ring

/-- All positive-order log-log derivatives have the exact strict alternating sign. -/
theorem signed_iteratedDeriv_logLog_pos (m : ℕ) {x : ℝ} (hx : 1 < x) :
    0 < (-1 : ℝ) ^ m *
      iteratedDeriv (m + 1) (fun y : ℝ => Real.log (Real.log y)) x := by
  rw [iteratedDeriv_logLog_eq m hx]
  have hsign : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc, hsign, one_mul]
  exact positiveKernel_pos m 0 0 hx

#print axioms signed_iteratedDeriv_logLog_pos

end D5.S3.Arith.Robin.LogLogHigherDerivative
