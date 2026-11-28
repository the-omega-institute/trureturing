/- GID: D5/S3/Analysis/SquareRootCosine
   generality: G
   mirror-B: none(waiver:covered-by-strong-cpaxion-theta-vacuum4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Derivatives of a positive square root with a cosine radicand at a cosine maximum. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Omega original.

Derivatives of a positive square root with a cosine radicand at a cosine maximum.
The fourth-order identity follows by differentiating the squared function.
-/

compile_only_with_mathlib

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace OmegaMath.SquareRootCosine

/-- Positive branch of the square root of a shifted cosine. -/
def profile (s p w : ℝ) (x : ℝ) : ℝ :=
  Real.sqrt (s ^ 2 + 2 * p * (Real.cos (w * x) - 1))

/-- The radicand stays positive in a neighborhood of zero when its square root there is positive. -/
theorem contDiffAt_profile {s : ℝ} (hs : 0 < s) (p w : ℝ) (n : ℕ) :
    ContDiffAt ℝ n (profile s p w) 0 := by
  unfold profile
  have h : ContDiff ℝ n (fun x : ℝ => s ^ 2 + 2 * p * (Real.cos (w * x) - 1)) := by
    fun_prop
  exact h.contDiffAt.sqrt (by simpa using pow_ne_zero 2 hs.ne')

private theorem radicand_deriv (s p w : ℝ) {n : ℕ} (hn : 0 < n) :
    iteratedDeriv n (fun x : ℝ => s ^ 2 + 2 * p * (Real.cos (w * x) - 1)) 0 =
      (2 * p) * w ^ n * iteratedDeriv n Real.cos 0 := by
  have he : (fun x : ℝ => s ^ 2 + 2 * p * (Real.cos (w * x) - 1)) =
      fun x => (s ^ 2 - 2 * p) + (2 * p) * Real.cos (w * x) := by
    funext x
    ring
  rw [he, iteratedDeriv_const_add hn, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul Real.contDiff_cos]
  simp [mul_assoc]

/-- At zero the first derivative vanishes, and the second and fourth derivatives have exact values. -/
theorem profile_derivatives {s : ℝ} (hs : 0 < s) (p w : ℝ) :
    HasDerivAt (profile s p w) 0 0 ∧
    HasDerivAt (deriv (profile s p w)) (-(p * w ^ 2 / s)) 0 ∧
    iteratedDeriv 4 (profile s p w) 0 = p * w ^ 4 / s - 3 * p ^ 2 * w ^ 4 / s ^ 3 := by
  let f := profile s p w
  have hval : f 0 = s := by simp [f, profile, Real.sqrt_sq hs.le]
  have hc (n : ℕ) : ContDiffAt ℝ n f 0 := contDiffAt_profile hs p w n
  have hq : ∀ᶠ x : ℝ in 𝓝 0, 0 < s ^ 2 + 2 * p * (Real.cos (w * x) - 1) := by
    have h : ContinuousAt (fun x : ℝ => s ^ 2 + 2 * p * (Real.cos (w * x) - 1)) 0 := by
      fun_prop
    apply h.eventually
    exact Ioi_mem_nhds (by simpa using sq_pos_of_pos hs)
  have hsq : (fun x => f x * f x) =ᶠ[𝓝 0]
      (fun x => s ^ 2 + 2 * p * (Real.cos (w * x) - 1)) := by
    filter_upwards [hq] with x hx
    exact Real.mul_self_sqrt hx.le
  have he (n : ℕ) (hn : 0 < n) :
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * iteratedDeriv i f 0 *
        iteratedDeriv (n - i) f 0) =
        (2 * p) * w ^ n * iteratedDeriv n Real.cos 0 := by
    rw [← iteratedDeriv_fun_mul (hc n) (hc n), hsq.iteratedDeriv_eq n, radicand_deriv _ _ _ hn]
  have h₁ : iteratedDeriv 1 f 0 = 0 := by
    have h := he 1 (by decide)
    norm_num [Finset.sum_range_succ, iteratedDeriv_zero, hval, iteratedDeriv_one,
      Real.deriv_cos] at h ⊢
    exact (mul_eq_zero.mp (by linear_combination h / 2 : s * deriv f 0 = 0)).resolve_left hs.ne'
  have h₂ : iteratedDeriv 2 f 0 = -(p * w ^ 2 / s) := by
    have hcos : iteratedDeriv 2 Real.cos 0 = -1 := by
      simp
    have h := he 2 (by decide)
    norm_num [Finset.sum_range_succ, iteratedDeriv_zero, hval, h₁, hcos] at h
    rw [← neg_div]
    apply (eq_div_iff hs.ne').mpr
    linear_combination h / 2
  have h₄ : iteratedDeriv 4 f 0 = p * w ^ 4 / s - 3 * p ^ 2 * w ^ 4 / s ^ 3 := by
    have hcos : iteratedDeriv 4 Real.cos 0 = 1 := by
      simp
    have h := he 4 (by decide)
    norm_num [Finset.sum_range_succ, iteratedDeriv_zero, hval, h₁, h₂, hcos, Nat.choose] at h
    field_simp [hs.ne'] at h ⊢
    linear_combination h / 2
  have hd1 : DifferentiableAt ℝ f 0 := (hc 1).differentiableAt (by decide)
  have hd2 : DifferentiableAt ℝ (deriv f) 0 :=
    ((hc 2).derivWithin (m := 1) (by decide)).differentiableAt (by decide)
  rw [iteratedDeriv_one] at h₁
  rw [show (2 : ℕ) = 1 + 1 by decide, iteratedDeriv_succ, iteratedDeriv_one] at h₂
  refine ⟨?_, ?_, h₄⟩
  · simpa only [h₁] using hd1.hasDerivAt
  · simpa only [h₂] using hd2.hasDerivAt

end OmegaMath.SquareRootCosine
