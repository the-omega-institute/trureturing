/- GID: D5/S3/Zeros/CriticalPoints/TangZhangConstantRoots
   generality: G
   mirror-B: D5/B/S3/Zeros/CriticalPoints/TangZhangConstantRoots
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Roots]
   utility: none
   digest: The exact critical-point moment when all nonzero polynomial roots coincide. -/

import D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Constant nonzero roots attain the real-order Tang–Zhang coefficient. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Zeros.CriticalPoints.TangZhangConstantRoots

open Polynomial
open TangZhangOrderMinusTwo (P)

private theorem derivative_constant (m : ℕ) (a : ℂ) :
    derivative (P (fun _ : Fin (m + 1) => a)) =
      C ((m : ℂ) + 2) * ((X - C a) ^ m * (X - C (a / ((m : ℂ) + 2)))) := by
  have hn : (m : ℂ) + 2 ≠ 0 := by
    have hr : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    exact_mod_cast ne_of_gt hr
  have hd : (C ((m : ℂ) + 2) : ℂ[X]) * C (a / ((m : ℂ) + 2)) = C a := by
    rw [← map_mul, mul_div_cancel₀ _ hn]
  calc
    derivative (P (fun _ : Fin (m + 1) => a)) =
        (X - C a) ^ m * (C ((m : ℂ) + 2) * X - C a) := by
      have hP : P (fun _ : Fin (m + 1) => a) = X * (X - C a) ^ (m + 1) := by
        simp only [P, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [hP, derivative_mul, derivative_X, one_mul, derivative_X_sub_C_pow,
        Nat.add_sub_cancel, pow_succ]
      simp only [Nat.cast_add, Nat.cast_one, map_add, map_ofNat, map_one]
      ring
    _ = C ((m : ℂ) + 2) * ((X - C a) ^ m * (X - C (a / ((m : ℂ) + 2)))) := by
      linear_combination (X - C a) ^ m * hd

private theorem roots_constant (m : ℕ) (a : ℂ) :
    (derivative (P (fun _ : Fin (m + 1) => a))).roots =
      m • ({a} : Multiset ℂ) + {a / ((m : ℂ) + 2)} := by
  have hn : (m : ℂ) + 2 ≠ 0 := by
    have hr : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    exact_mod_cast ne_of_gt hr
  rw [derivative_constant, roots_C_mul _ hn,
    roots_mul (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)),
    roots_pow, roots_X_sub_C, roots_X_sub_C]

/-- Coincident nonzero roots attain the asserted coefficient at every real order. -/
theorem constant_roots_moment (n : ℕ) (hn : 1 ≤ n) (a : ℂ) (ha : a ≠ 0) (p : ℝ) :
    ((derivative (P (fun _ : Fin n => a))).roots.map (fun w => ‖w‖ ^ (-p))).sum =
      ((((n : ℝ) + 1) ^ p + n - 1) / n) * ∑ _ : Fin n, ‖a‖ ^ (-p) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  have hnorm : ‖((m : ℂ) + 2)‖ = (m : ℝ) + 2 := by
    convert Complex.norm_of_nonneg (show (0 : ℝ) ≤ (m : ℝ) + 2 by positivity) using 1 <;>
      push_cast <;> rfl
  have hmoment : ‖a / ((m : ℂ) + 2)‖ ^ (-p) = ((m : ℝ) + 2) ^ p * ‖a‖ ^ (-p) := by
    rw [norm_div, hnorm, Real.div_rpow (norm_nonneg _) (by positivity),
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 2)]
    simp only [div_inv_eq_mul, mul_comm]
  rw [roots_constant]
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.nsmul_singleton,
    Multiset.map_replicate, Multiset.map_singleton, Multiset.sum_replicate,
    Multiset.sum_singleton, nsmul_eq_mul, hmoment, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  have hn' : (m : ℝ) + 1 ≠ 0 := by positivity
  rw [show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring]
  field_simp [hn']
  ring

end D5.S3.Zeros.CriticalPoints.TangZhangConstantRoots
