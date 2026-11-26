/- GID: D5/S3/Quantum/Algebra/Comparison/QuaternionHeapRecurrence
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/Comparison/QuaternionHeapRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The quaternion heap recurrence has a Chebyshev closed form. -/

import Mathlib.Analysis.Quaternion
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Chebyshev formulas for the quaternion heap recurrence -/

open scoped InnerProductSpace Quaternion
open Polynomial.Chebyshev

namespace D5.S3.Quantum.Algebra.Comparison.QuaternionHeapRecurrence

private theorem reflect (x w : ℍ[ℝ]) :
    x * star w * x = (2 * ⟪x, w⟫_ℝ) • x - Quaternion.normSq x • w := by
  have hsum : x * star w + w * star x = ((2 * ⟪x, w⟫_ℝ : ℝ) : ℍ[ℝ]) := by
    simpa [star_mul, Quaternion.inner_def] using Quaternion.self_add_star' (x * star w)
  rw [← Quaternion.coe_mul_eq_smul, ← Quaternion.mul_coe_eq_smul, ← hsum, add_mul,
    mul_assoc w, Quaternion.star_mul_self]
  abel

private theorem interfere (x w y : ℍ[ℝ]) (hx : Quaternion.normSq x = 1) :
    ⟪y, x * star w * x⟫_ℝ + ⟪y, w⟫_ℝ = 2 * ⟪x, w⟫_ℝ * ⟪y, x⟫_ℝ := by
  rw [reflect, hx, one_smul, inner_sub_right, real_inner_smul_right]
  abel

private theorem eval_U_recurrence (c : ℝ) (m : ℤ) :
    (U ℝ m).eval c = 2 * c * (U ℝ (m - 1)).eval c - (U ℝ (m - 2)).eval c := by
  rw [U_eq ℝ m]
  simp

private noncomputable def chebyshevSample (c : ℝ) (first second : ℍ[ℝ]) (n : ℕ) : ℍ[ℝ] :=
  (U ℝ ((n : ℤ) - 1)).eval c • second - (U ℝ ((n : ℤ) - 2)).eval c • first

private theorem chebyshevSample_recurrence (c : ℝ) (first second : ℍ[ℝ]) (n : ℕ) :
    chebyshevSample c first second (n + 2) =
      (2 * c) • chebyshevSample c first second (n + 1) - chebyshevSample c first second n := by
  unfold chebyshevSample
  have ha : ((n + 2 : ℕ) : ℤ) - 1 = (n : ℤ) + 1 := by omega
  have hb : ((n + 2 : ℕ) : ℤ) - 2 = (n : ℤ) := by omega
  have hc : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
  have hd : ((n + 1 : ℕ) : ℤ) - 2 = (n : ℤ) - 1 := by omega
  rw [ha, hb, hc, hd, eval_U_recurrence c ((n : ℤ) + 1)]
  simp only [show (n : ℤ) + 1 - 1 = n by omega, show (n : ℤ) + 1 - 2 = n - 1 by omega,
    eval_U_recurrence c (n : ℤ)]
  module

private theorem closed_of_recurrence (x : ℕ → ℍ[ℝ])
    (h0 : Quaternion.normSq (x 0) = 1) (h1 : Quaternion.normSq (x 1) = 1)
    (hrec : ∀ n, x (n + 2) = x (n + 1) * star (x n) * x (n + 1)) :
    ∀ n : ℕ, Quaternion.normSq (x n) = 1 ∧
      x (n + 1) = (U ℝ (n : ℤ)).eval ⟪x 0, x 1⟫_ℝ • x 1 -
        (U ℝ ((n : ℤ) - 1)).eval ⟪x 0, x 1⟫_ℝ • x 0 ∧
      ⟪x 0, x n⟫_ℝ = (T ℝ (n : ℤ)).eval ⟪x 0, x 1⟫_ℝ := by
  let c : ℝ := ⟪x 0, x 1⟫_ℝ
  have hunit : ∀ n, Quaternion.normSq (x n) = 1 := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => exact h0
    | one => exact h1
    | more n ih₀ ih₁ =>
      rw [hrec n, map_mul, map_mul, Quaternion.normSq_star, ih₀, ih₁, mul_one, mul_one]
  have hadj : ∀ n, ⟪x n, x (n + 1)⟫_ℝ = c := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have h := interfere (x (n + 1)) (x n) (x (n + 1)) (hunit (n + 1))
      rw [← hrec n, Quaternion.inner_self, hunit, mul_one,
        real_inner_comm (x n) (x (n + 1)), ih] at h
      change ⟪x (n + 1), x (n + 2)⟫_ℝ = c
      linear_combination h
  have hlinear (n : ℕ) : x (n + 2) = (2 * c) • x (n + 1) - x n := by
    rw [hrec n, reflect, hunit, one_smul, real_inner_comm (x n) (x (n + 1)), hadj n]
  let u : ℤ → ℝ := fun m => (U ℝ m).eval c
  have hformula : ∀ n : ℕ, x n = chebyshevSample c (x 0) (x 1) n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => norm_num [chebyshevSample, U_neg_two]
    | one => norm_num [chebyshevSample]
    | more n ih₀ ih₁ => rw [hlinear n, ih₀, ih₁, chebyshevSample_recurrence]
  intro n
  refine ⟨hunit n, ?_, ?_⟩
  · have he := hformula (n + 1)
    unfold chebyshevSample at he
    rw [show ((n + 1 : ℕ) : ℤ) - 1 = n by omega,
      show ((n + 1 : ℕ) : ℤ) - 2 = (n : ℤ) - 1 by omega] at he
    exact he
  · calc
      ⟪x 0, x n⟫_ℝ = u ((n : ℤ) - 1) * c - u ((n : ℤ) - 2) := by
        conv_lhs => rw [hformula n, chebyshevSample]
        rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right,
          Quaternion.inner_self, h0, mul_one]
      _ = (T ℝ (n : ℤ)).eval c := by
        rw [T_eq_U_sub_X_mul_U, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
        change _ = u (n : ℤ) - c * u ((n : ℤ) - 1)
        rw [show u (n : ℤ) = 2 * c * u ((n : ℤ) - 1) - u ((n : ℤ) - 2)
          from eval_U_recurrence c (n : ℤ)]
        ring

/-- Unit normalization and the cubic recurrence are equivalent to the Chebyshev formulas
for the samples and their comparison with the initial point. -/
theorem normSq_and_chebyshev (x : ℕ → ℍ[ℝ]) :
    (Quaternion.normSq (x 0) = 1 ∧ Quaternion.normSq (x 1) = 1 ∧
      ∀ n, x (n + 2) = x (n + 1) * star (x n) * x (n + 1)) ↔
    ∀ n : ℕ, Quaternion.normSq (x n) = 1 ∧
      x (n + 1) = (U ℝ (n : ℤ)).eval ⟪x 0, x 1⟫_ℝ • x 1 -
        (U ℝ ((n : ℤ) - 1)).eval ⟪x 0, x 1⟫_ℝ • x 0 ∧
      ⟪x 0, x n⟫_ℝ = (T ℝ (n : ℤ)).eval ⟪x 0, x 1⟫_ℝ := by
  constructor
  · rintro ⟨h0, h1, hrec⟩
    exact closed_of_recurrence x h0 h1 hrec
  · intro h
    let c : ℝ := ⟪x 0, x 1⟫_ℝ
    have hunit (n : ℕ) : Quaternion.normSq (x n) = 1 := (h n).1
    have hformula (n : ℕ) : x n = chebyshevSample c (x 0) (x 1) n := by
      cases n with
      | zero => norm_num [chebyshevSample, U_neg_two]
      | succ n =>
        unfold chebyshevSample
        rw [show (↑n.succ : ℤ) - 1 = n by omega,
          show (↑n.succ : ℤ) - 2 = (n : ℤ) - 1 by omega]
        exact (h n).2.1
    have hlinear (n : ℕ) : x (n + 2) = (2 * c) • x (n + 1) - x n := by
      calc
        x (n + 2) = chebyshevSample c (x 0) (x 1) (n + 2) := hformula (n + 2)
        _ = (2 * c) • chebyshevSample c (x 0) (x 1) (n + 1) -
            chebyshevSample c (x 0) (x 1) n := chebyshevSample_recurrence c (x 0) (x 1) n
        _ = (2 * c) • x (n + 1) - x n := by rw [← hformula (n + 1), ← hformula n]
    have hadj : ∀ n, ⟪x n, x (n + 1)⟫_ℝ = c := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        change ⟪x (n + 1), x (n + 2)⟫_ℝ = c
        rw [hlinear n, inner_sub_right, real_inner_smul_right, Quaternion.inner_self,
          hunit (n + 1), mul_one, real_inner_comm (x n) (x (n + 1)), ih]
        ring
    refine ⟨hunit 0, hunit 1, fun n => ?_⟩
    rw [hlinear n, reflect, hunit (n + 1), one_smul,
      real_inner_comm (x n) (x (n + 1)), hadj n]

end D5.S3.Quantum.Algebra.Comparison.QuaternionHeapRecurrence
