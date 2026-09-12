/- GID: D5/S1/Recurrence/Residue/LogarithmicWeightBinaryParity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/LogarithmicWeightBinaryParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Differentiation identifies logarithmic-weight parity with binary Catalan support. -/

import D5.S1.Recurrence.Residue.LogarithmicWeightCatalanParity
import D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open PowerSeries
open scoped BigOperators

namespace D5.S1.Recurrence.Residue.LogarithmicWeightBinaryParity

open LogarithmicWeightCatalanParity (s a b s_zero s_one a_one)
open Invariants.CatalanCompositionSquareParity (catalanSeries catalan_equation binary_catalan)
open private s_eq_sum from D5.S1.Recurrence.Residue.LogarithmicWeightCatalanParity
open private quadratic_unique from D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity

private noncomputable def A : PowerSeries (ZMod 2) := mk fun n => (a n : ZMod 2)
private noncomputable def C : PowerSeries (ZMod 2) :=
  mk fun n => if n = 0 then 0 else (b n : ZMod 2)
private noncomputable def S : PowerSeries (ZMod 2) := mk fun n => (s n : ZMod 2)

private theorem A_quadratic : A = X + A ^ 2 := by
  have a_zero : a 0 = 0 := by simp [a, s_zero]
  have coeff_A : ∀ n : ℕ, n ≠ 1 →
      coeff n A = ((n : ZMod 2) + 1) * (s n : ZMod 2) := by
    intro n hn
    simp only [A, coeff_mk, a, if_neg hn, Int.cast_mul, Int.cast_sub,
      Int.cast_ofNat, Int.cast_pow, Int.cast_natCast, Int.cast_one]
    simp [CharTwo.ofNat_eq_mod, ZMod.pow_card, CharTwo.sub_eq_add]
  have coeff_C : ∀ n : ℕ, 2 ≤ n →
      coeff n C = (n : ZMod 2) * (s n : ZMod 2) := by
    intro n hn
    simp [C, b, show n ≠ 0 by omega, show ¬n ≤ 1 by omega, CharTwo.ofNat_eq_mod]
  have deriv_A : derivative (ZMod 2) A = 1 := by
    ext n
    rw [coeff_derivative, coeff_one]
    by_cases hn : n = 0
    · subst n
      simp [A, a_one]
    · rw [if_neg hn, coeff_A (n + 1) (by omega)]
      have h := ZMod.pow_card ((n : ZMod 2) + 1)
      have hz2 : (2 : ZMod 2) = 0 := CharTwo.two_eq_zero
      push_cast
      linear_combination (s (n + 1) : ZMod 2) * h +
        (((n : ZMod 2) + 1) * (s (n + 1) : ZMod 2)) * hz2
  have S_eq_mul : S = A * C := by
    ext n
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [A, C, S, coeff_mk]
    by_cases hn0 : n = 0
    · subst n
      simp [s_zero]
    by_cases hn1 : n = 1
    · subst n
      simp [Finset.sum_range_succ, s_one, a_zero]
    rw [Finset.sum_range_succ']
    simp only [a_zero, Int.cast_zero, zero_mul, add_zero]
    have hn : n = (n - 1) + 1 := by omega
    rw [show Finset.range n = Finset.range ((n - 1) + 1) by rw [← hn]]
    rw [Finset.sum_range_succ]
    simp only [show n - 1 + 1 = n by omega, Nat.sub_self, ite_true, mul_zero, add_zero]
    rw [s_eq_sum n (by omega), Int.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : n - (j + 1) ≠ 0 := by simp only [Finset.mem_range] at hj; omega
    simp [hjn]
  have A_eq_add_mul : A = C + A * C := by
    rw [← S_eq_mul]
    ext n
    rw [map_add]
    by_cases hn0 : n = 0
    · subst n
      simp [A, C, S, a_zero, s_zero]
    by_cases hn1 : n = 1
    · subst n
      simp [A, C, S, a_one, b, s_one]
    rw [coeff_A n hn1, coeff_C n (by omega)]
    simp only [S, coeff_mk]
    ring
  have C_eq_X_deriv : C = X * (1 + derivative (ZMod 2) S) := by
    ext n
    cases n with
    | zero => simp [C]
    | succ n =>
      rw [coeff_succ_X_mul, map_add, coeff_one, coeff_derivative]
      by_cases hn : n = 0
      · subst n
        simp [C, S, b, s_one]
      · rw [if_neg hn, zero_add, coeff_C (n + 1) (by omega)]
        simp [S, mul_comm]
  have hz : (2 : PowerSeries (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (PowerSeries.C (R := ZMod 2))
        (show (2 : ZMod 2) = 0 from CharTwo.two_eq_zero)
  have he := A_eq_add_mul
  have hd := congrArg (derivative (ZMod 2)) he
  simp only [map_add, Derivation.leibniz, smul_eq_mul, deriv_A, mul_one] at hd
  have hdc : derivative (ZMod 2) C * (1 + A) = 1 + C := by
    linear_combination -hd - C * hz
  have hds := congrArg (derivative (ZMod 2)) S_eq_mul
  simp only [Derivation.leibniz, smul_eq_mul, deriv_A, mul_one] at hds
  have hbracket : 1 + (A * derivative (ZMod 2) C + C) = derivative (ZMod 2) C := by
    linear_combination hd + (A * derivative (ZMod 2) C + C) * hz
  have hc : C = X * derivative (ZMod 2) C := calc
    C = X * (1 + derivative (ZMod 2) S) := C_eq_X_deriv
    _ = X * derivative (ZMod 2) C := by rw [hds, hbracket]
  have hu : (1 + C) * (1 + A) = 1 := by
    linear_combination he + (C + A * C) * hz
  have hprod : A * (1 + A) = X := calc
    A * (1 + A) = C * (1 + A) ^ 2 := by linear_combination (1 + A) * he
    _ = X * (derivative (ZMod 2) C * (1 + A)) * (1 + A) := by
      conv_lhs => rw [hc]
      ring
    _ = X := by rw [hdc, mul_assoc, hu, mul_one]
  linear_combination hprod - A ^ 2 * hz

theorem parity_conjecture_holds : LogarithmicWeightCatalanParity.parity_conjecture := by
  have a_zero : a 0 = 0 := by simp [a, s_zero]
  have hA0 : constantCoeff A = 0 := by
    rw [← coeff_zero_eq_constantCoeff]
    simp [A, a_zero]
  have hcat0 : constantCoeff (catalanSeries.map (Int.castRingHom (ZMod 2))) = 0 := by
    rw [← coeff_zero_eq_constantCoeff]
    simp only [coeff_map, coeff_zero_eq_constantCoeff, catalan_equation.1, map_zero]
  have hcat : catalanSeries.map (Int.castRingHom (ZMod 2)) =
      X + (catalanSeries.map (Int.castRingHom (ZMod 2))) ^ 2 := by
    simpa using congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) catalan_equation.2.2
  have hA := quadratic_unique hA0 hcat0 A_quadratic hcat
  intro n
  rw [← ZMod.intCast_eq_one_iff_odd]
  have hcoeff : coeff n A = (a n : ZMod 2) := coeff_mk n _
  rw [← hcoeff, hA]
  exact binary_catalan n

#print axioms parity_conjecture_holds

end D5.S1.Recurrence.Residue.LogarithmicWeightBinaryParity
