/- GID: D5/S3/Zeros/CriticalPoints/TangZhangRealOrderCounterexample
   generality: G
   mirror-B: D5/B/S3/Zeros/CriticalPoints/TangZhangRealOrderCounterexample
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Roots]
   utility: none
   digest: The order-minus-one equality clause fails for distinct positive roots. -/

import D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FinCases

/-! An explicit counterexample to the real-order-one equality characterization. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Zeros.CriticalPoints.TangZhangRealOrderCounterexample

open Polynomial
open TangZhangOrderMinusTwo (P)

private theorem explicit_roots :
    (derivative (P ![(1 : ℂ), 2])).roots =
      {((1 - Real.sqrt 3 / 3 : ℝ) : ℂ), ((1 + Real.sqrt 3 / 3 : ℝ) : ℂ)} := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsc : ((Real.sqrt 3 : ℂ)) ^ 2 = 3 := by exact_mod_cast hs
  have hf : derivative (P ![(1 : ℂ), 2]) =
      C (3 : ℂ) * ((X - C ((1 - Real.sqrt 3 / 3 : ℝ) : ℂ)) *
        (X - C ((1 + Real.sqrt 3 / 3 : ℝ) : ℂ))) := by
    simp only [P, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      derivative_mul, derivative_X_sub_C, derivative_X]
    have hab : ((1 - Real.sqrt 3 / 3 : ℝ) : ℂ) +
        ((1 + Real.sqrt 3 / 3 : ℝ) : ℂ) = 2 := by push_cast; ring
    have hprod : (3 : ℂ) * ((1 - Real.sqrt 3 / 3 : ℝ) : ℂ) *
        ((1 + Real.sqrt 3 / 3 : ℝ) : ℂ) = 2 := by
      push_cast
      linear_combination -(1 / 3 : ℂ) * hsc
    have habC : (C ((1 - Real.sqrt 3 / 3 : ℝ) : ℂ) +
        C ((1 + Real.sqrt 3 / 3 : ℝ) : ℂ) : ℂ[X]) = 2 := by
      simpa only [map_add, map_ofNat] using congrArg (C : ℂ →+* ℂ[X]) hab
    have hprodC : (3 : ℂ[X]) * C ((1 - Real.sqrt 3 / 3 : ℝ) : ℂ) *
        C ((1 + Real.sqrt 3 / 3 : ℝ) : ℂ) = 2 := by
      simpa only [map_mul, map_ofNat] using congrArg (C : ℂ →+* ℂ[X]) hprod
    norm_num only [map_one, map_ofNat]
    linear_combination (3 * X) * habC - hprodC
  rw [hf, roots_C_mul _ (by norm_num), roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C]
  rfl

private theorem explicit_sum :
    ((derivative (P ![(1 : ℂ), 2])).roots.map (fun w => ‖w‖ ^ (-(1 : ℝ)))).sum = 3 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hsl : Real.sqrt 3 < 3 := by nlinarith
  have ha : 0 < 1 - Real.sqrt 3 / 3 := by linarith
  have hb : 0 < 1 + Real.sqrt 3 / 3 := by linarith
  rw [explicit_roots]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
    Multiset.sum_singleton, Real.rpow_neg_one, Complex.norm_real,
    Real.norm_of_nonneg ha.le, Real.norm_of_nonneg hb.le]
  field_simp
  nlinarith

/-- The proposed equality characterization at real order one fails. -/
theorem counterexample :
    ¬ (∀ (n : ℕ) (z : Fin n → ℂ), (∀ j, z j ≠ 0) →
       (((derivative (P z)).roots.map (fun w => ‖w‖ ^ (-(1 : ℝ)))).sum =
         ((((n : ℝ) + 1) ^ (1 : ℝ) + n - 1) / n) *
           ∑ j, ‖z j‖ ^ (-(1 : ℝ)) ↔ ∀ i j, z i = z j)) := by
  intro h
  have hz : ∀ j : Fin 2, ![(1 : ℂ), 2] j ≠ 0 := by
    intro j
    fin_cases j <;> norm_num
  have he : ((derivative (P ![(1 : ℂ), 2])).roots.map
      (fun w => ‖w‖ ^ (-(1 : ℝ)))).sum =
      ((((2 : ℝ) + 1) ^ (1 : ℝ) + 2 - 1) / 2) *
        ∑ j : Fin 2, ‖![(1 : ℂ), 2] j‖ ^ (-(1 : ℝ)) := by
    rw [explicit_sum]
    norm_num [Fin.sum_univ_two, Real.rpow_neg_one]
  have hc := (h 2 ![(1 : ℂ), 2] hz).mp he (0 : Fin 2) (1 : Fin 2)
  norm_num at hc

end D5.S3.Zeros.CriticalPoints.TangZhangRealOrderCounterexample
