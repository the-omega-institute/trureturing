/- GID: D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialColumnFamily
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/AffinePolynomialPairBinomialColumnFamily
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.WellKnown]
   utility: none
   digest: h_d(m) = [z^m](1+z)/(1-z)^d: closed forms, sums, recurrence, polynomial symmetry. -/

import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Algebra.Polynomial.BigOperators

/-! The binomial column family `h_d` of the affine polynomial pair. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialColumnFamily

open Finset

section
open PowerSeries

/-- `h_d(m) = [z^m] (1 + z)/(1 - z)^d`. -/
noncomputable def h (d m : ℕ) : ℤ := coeff m ((1 + X) * (invOneSubPow ℤ d).val)

private theorem h_eq (d m : ℕ) (hd : 2 ≤ d) :
    h d m = (Nat.choose (m + d - 1) (d - 1) : ℤ) + Nat.choose (m + d - 2) (d - 1) := by
  rw [h, invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos _ _ (by omega), add_mul, one_mul,
    map_add, coeff_mk]
  rcases m with _ | m
  · simp [Nat.choose_eq_zero_of_lt (show d - 2 < d - 1 by omega)]
  · rw [mul_comm, coeff_succ_mul_X, coeff_mk]
    rw [show d - 1 + (m + 1) = m + 1 + d - 1 by omega, show d - 1 + m = m + 1 + d - 2 by omega]

private theorem h_alt (d m : ℕ) (hd : 2 ≤ d) :
    h d m = 2 * (Nat.choose (m + d - 1) (d - 1) : ℤ) - Nat.choose (m + d - 2) (d - 2) ∧
    ((d : ℚ) - 1) * h d m = (2 * m + d - 1) * Nat.choose (m + d - 2) (d - 2) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  rw [h_eq _ _ hd]
  simp only [show m + (e + 2) - 1 = (m + e) + 1 by omega, show e + 2 - 1 = e + 1 by omega,
    show m + (e + 2) - 2 = m + e by omega, show e + 2 - 2 = e by omega]
  have hp : (Nat.choose (m + e + 1) (e + 1) : ℤ) =
      Nat.choose (m + e) e + Nat.choose (m + e) (e + 1) := by
    rw [Nat.choose_succ_succ']; push_cast; ring
  have hs := Nat.add_one_mul_choose_eq (m + e) e
  constructor
  · rw [hp]; ring
  · have hs' : ((m + e + 1 : ℕ) : ℚ) * Nat.choose (m + e) e =
        Nat.choose (m + e + 1) (e + 1) * (e + 1 : ℕ) := by exact_mod_cast hs
    have hp' : (Nat.choose (m + e + 1) (e + 1) : ℚ) =
        Nat.choose (m + e) e + Nat.choose (m + e) (e + 1) := by exact_mod_cast hp
    push_cast at hs' ⊢
    linear_combination (-2 : ℚ) * hs' - ((e : ℚ) + 1) * hp'

private theorem h_cumulative (d m : ℕ) : h (d + 1) m = ∑ j ∈ range (m + 1), h d j := by
  simp only [h]
  rw [invOneSubPow_add, Units.val_mul, ← mul_assoc]
  have h1 : (invOneSubPow ℤ 1).val = mk 1 := by
    rw [invOneSubPow_val_succ_eq_mk_add_choose]; ext n; simp
  rw [h1, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp

private theorem h_gf (d : ℕ) : (1 - X : ℤ⟦X⟧) ^ d * ((1 + X) * (invOneSubPow ℤ d).val) = 1 + X := by
  have hv : (invOneSubPow ℤ d).val * (1 - X) ^ d = 1 := by
    rw [← invOneSubPow_inv_eq_one_sub_pow]; exact (invOneSubPow ℤ d).val_inv
  calc (1 - X : ℤ⟦X⟧) ^ d * ((1 + X) * (invOneSubPow ℤ d).val)
      = (1 + X) * ((invOneSubPow ℤ d).val * (1 - X) ^ d) := by ring
    _ = 1 + X := by rw [hv, mul_one]

private theorem one_sub_pow_expand (d : ℕ) : (1 - X : ℤ⟦X⟧) ^ d =
    ∑ j ∈ range (d + 1), C ((-1) ^ j * (d.choose j : ℤ)) * X ^ j := by
  rw [show (1 - X : ℤ⟦X⟧) = -X + 1 by ring, add_pow]
  apply sum_congr rfl
  intro j _
  rw [one_pow, mul_one, neg_pow, map_mul, map_pow, map_neg, map_one, map_natCast]
  ring

private theorem h_rec (d m : ℕ) (hm2 : 2 ≤ m) :
    h d m = ∑ j ∈ Icc 1 (min d m), (-1) ^ (j + 1) * (d.choose j : ℤ) * h d (m - j) := by
  have key := congrArg (coeff m) (h_gf d)
  rw [one_sub_pow_expand, sum_mul, map_sum, map_add, coeff_one, coeff_X] at key
  simp only [show m ≠ 0 by omega, show m ≠ 1 by omega, ↓reduceIte, add_zero] at key
  have hterm : ∀ j ∈ range (d + 1), coeff m (C ((-1) ^ j * (d.choose j : ℤ)) * X ^ j *
      ((1 + X) * (invOneSubPow ℤ d).val)) =
        if j ≤ m then (-1) ^ j * (d.choose j : ℤ) * h d (m - j) else 0 := by
    intro j _
    rw [mul_assoc, coeff_C_mul, mul_comm (X ^ j), coeff_mul_X_pow']
    split_ifs <;> simp [h]
  rw [sum_congr rfl hterm, ← sum_filter] at key
  have hf : (range (d + 1)).filter (fun j => j ≤ m) = range (min d m + 1) := by
    ext j; simp only [mem_filter, mem_range]; omega
  rw [hf, sum_range_succ'] at key
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero, one_mul] at key
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  have : ∑ k ∈ range (min d m), (-1) ^ (1 + k + 1) * (d.choose (1 + k) : ℤ) * h d (m - (1 + k)) =
      -∑ i ∈ range (min d m), (-1) ^ (i + 1) * (d.choose (i + 1) : ℤ) * h d (m - (i + 1)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    rw [show 1 + i = i + 1 by ring, pow_succ]
    ring
  rw [this]
  linarith

end

section
open Polynomial

/-- The polynomial extension `H_d(t) = (2t + d - 1)/(d - 1)! · ∏_{i=1}^{d-2} (t + i)`. -/
noncomputable def H (d : ℕ) : Polynomial ℚ :=
  C (2 / ((d - 1).factorial : ℚ)) * (X + C (((d : ℚ) - 1) / 2)) *
    ∏ i ∈ range (d - 2), (X + C ((i : ℚ) + 1))

private theorem H_eval (d m : ℕ) (hd : 2 ≤ d) : (H d).eval (m : ℚ) = h d m := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have halt := (h_alt (e + 2) m hd).2
  simp only [show e + 2 - 2 = e by omega, show m + (e + 2) - 2 = m + e by omega] at halt
  have hasc := Nat.ascFactorial_eq_factorial_mul_choose m e
  rw [Nat.ascFactorial_eq_prod_range] at hasc
  have hasc' : (∏ i ∈ range e, ((m : ℚ) + 1 + i)) = (e.factorial : ℚ) * Nat.choose (m + e) e := by
    exact_mod_cast hasc
  simp only [H, eval_mul, eval_C, eval_add, eval_X, eval_prod, show e + 2 - 2 = e by omega,
    show e + 2 - 1 = e + 1 by omega]
  have hprod : ∏ i ∈ range e, ((m : ℚ) + ((i : ℚ) + 1)) =
      (e.factorial : ℚ) * Nat.choose (m + e) e := by
    rw [← hasc']; apply prod_congr rfl; intro i _; ring
  rw [hprod, Nat.factorial_succ]
  have he : ((e : ℚ) + 1) ≠ 0 := by positivity
  have hf : (e.factorial : ℚ) ≠ 0 := by positivity
  push_cast at halt ⊢
  field_simp
  linear_combination -halt

private theorem H_monic_part (d : ℕ) : ((X + C (((d : ℚ) - 1) / 2)) *
    ∏ i ∈ range (d - 2), (X + C ((i : ℚ) + 1))).Monic ∧
    ((X + C (((d : ℚ) - 1) / 2)) * ∏ i ∈ range (d - 2), (X + C ((i : ℚ) + 1))).natDegree =
      d - 2 + 1 := by
  have hm : (∏ i ∈ range (d - 2), (X + C ((i : ℚ) + 1))).Monic :=
    monic_prod_of_monic _ _ (fun i _ => monic_X_add_C _)
  have hdeg : (∏ i ∈ range (d - 2), (X + C ((i : ℚ) + 1))).natDegree = d - 2 := by
    rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C _)]
    simp only [natDegree_X_add_C, sum_const, card_range, smul_eq_mul, mul_one]
  refine ⟨(monic_X_add_C _).mul hm, ?_⟩
  rw [(monic_X_add_C _).natDegree_mul hm, natDegree_X_add_C, hdeg]
  ring

private theorem H_degree (d : ℕ) (hd : 2 ≤ d) : (H d).natDegree = d - 1 ∧
    (H d).leadingCoeff = 2 / ((d - 1).factorial : ℚ) := by
  obtain ⟨hmon, hdeg⟩ := H_monic_part d
  have hk : (2 / ((d - 1).factorial : ℚ)) ≠ 0 :=
    div_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  rw [H, mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [natDegree_C_mul hk, hdeg]; omega
  · rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hk), hmon.leadingCoeff, mul_one]

private theorem H_symm (d : ℕ) (hd : 2 ≤ d) (t : ℚ) :
    (H d).eval (-t - d + 1) = (-1) ^ (d - 1) * (H d).eval t := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  simp only [H, eval_mul, eval_C, eval_add, eval_X, eval_prod, show e + 2 - 2 = e by omega,
    show e + 2 - 1 = e + 1 by omega]
  have hrefl : ∏ i ∈ range e, (-t - ((e + 2 : ℕ) : ℚ) + 1 + ((i : ℚ) + 1)) =
      (-1) ^ e * ∏ i ∈ range e, (t + ((i : ℚ) + 1)) := by
    rw [← prod_range_reflect (fun i => t + ((i : ℚ) + 1)) e,
      show ((-1 : ℚ)) ^ e = ∏ _j ∈ range e, (-1 : ℚ) by simp, ← prod_mul_distrib]
    apply prod_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    rw [Nat.sub_sub, Nat.cast_sub (show 1 + i ≤ e by omega)]
    push_cast
    ring
  rw [hrefl, pow_succ]
  push_cast
  ring

end

/-- Corollary 6 of the Ma–Zhang note on A208509, for `h_d(m) = [z^m](1 + z)/(1 - z)^d`:
closed forms for `d ≥ 2`; the partial sums `h_(d+1)(m) = ∑_{j ≤ m} h_d(j)` for every `d`; the
finite-difference recurrence for every `d` and `m ≥ 2`, summed over `1 ≤ j ≤ min(d, m)`; and,
for `d ≥ 2`, the polynomial extension `H_d` of degree `d - 1`, leading coefficient `2/(d - 1)!` and reflection
`H_d(-t-d+1) = (-1)^(d-1) H_d(t)`. -/
theorem result :
    (∀ d m : ℕ, 2 ≤ d →
      h d m = (Nat.choose (m + d - 1) (d - 1) : ℤ) + Nat.choose (m + d - 2) (d - 1) ∧
      h d m = 2 * (Nat.choose (m + d - 1) (d - 1) : ℤ) - Nat.choose (m + d - 2) (d - 2) ∧
      (h d m : ℚ) = (2 * m + d - 1) / (d - 1) * Nat.choose (m + d - 2) (d - 2)) ∧
    (∀ d m : ℕ, h (d + 1) m = ∑ j ∈ range (m + 1), h d j) ∧
    (∀ d m : ℕ, 2 ≤ m →
      h d m = ∑ j ∈ Icc 1 (min d m), (-1) ^ (j + 1) * (d.choose j : ℤ) * h d (m - j)) ∧
    (∀ d : ℕ, 2 ≤ d → (∀ m : ℕ, (H d).eval (m : ℚ) = h d m) ∧ (H d).natDegree = d - 1 ∧
      (H d).leadingCoeff = 2 / ((d - 1).factorial : ℚ) ∧
      ∀ t : ℚ, (H d).eval (-t - d + 1) = (-1) ^ (d - 1) * (H d).eval t) := by
  refine ⟨fun d m hd => ⟨h_eq d m hd, (h_alt d m hd).1, ?_⟩, h_cumulative, h_rec,
    fun d hd => ⟨fun m => H_eval d m hd, (H_degree d hd).1, (H_degree d hd).2, H_symm d hd⟩⟩
  have h2 := (h_alt d m hd).2
  have hd1 : ((d : ℚ) - 1) ≠ 0 := by
    have : (2 : ℚ) ≤ d := by exact_mod_cast hd
    linarith
  rw [div_mul_eq_mul_div, eq_div_iff hd1, ← h2]
  ring

end D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialColumnFamily
