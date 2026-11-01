/- GID: D5/S3/ArithSums/BrowneA164660ChebyshevFloorProduct
   generality: I
   mirror-B: D5/B/S3/ArithSums/BrowneA164660ChebyshevFloorProduct
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Chebyshev row numerators equal Browne's floor product for every positive index. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#21736; Proved)
Direct frozen dependencies: none (Mathlib-only imports).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21792
The literal row-sum and floor expressions are those of OEIS A164660.
The integrated coefficient is inlined in rowSum: it is the corresponding
coefficient of the generic power-series primitive in SchroderIntegralEGF.
The proof uses polynomial coefficient and evaluation identities directly.
All private lemmas are bind-only; their consumers are:
  power_dvd_iff -> floor_product_eq
  quotient_even_iff -> result
  floor_indicator -> floor_product_eq
  floor_product_eq -> result
  primitive_derivative -> row_sum_primitive
  primitive_degree -> row_sum_primitive
  row_sum_primitive -> row_sum_evaluation
  cheb_zero_nat -> row_sum_evaluation
  row_sum_evaluation -> numerator_eq
  numerator_eq -> result
The private primitive is a rational polynomial, used by its derivative, degree
and endpoint lemmas. No nonbinding escape content is claimed.
-/

import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithSums.BrowneA164660ChebyshevFloorProduct

open scoped BigOperators

/-- Sum of the rational triangle row, equivalently the integral from 0 to 1. -/
noncomputable def rowSum (m : ℕ) : ℚ :=
  ∑ j ∈ Finset.Icc 1 (m + 1),
    (Polynomial.Chebyshev.T ℚ (m : ℤ)).coeff (j - 1) / (j : ℚ)

/-- A164660(m): reduced signed numerator, with positive denominator. -/
noncomputable def a (m : ℕ) : ℤ :=
  (rowSum m).num

/-- The literal floor product; subtraction takes place in ℚ before flooring. -/
noncomputable def floorProduct (n : ℕ) : ℤ :=
  ∏ k ∈ Finset.Icc 1 n,
    (1 - 2 * (⌊(k : ℚ) ^ n / (n : ℚ)⌋ -
      ⌊((k : ℚ) ^ n - 1) / (n : ℚ)⌋) : ℤ)

/-- Browne's entire final FORMULA, including n = 1 and both equalities. -/
def claim : Prop :=
  ∀ n : ℕ, 0 < n →
    a (n + 1) = floorProduct n ∧
      floorProduct n = (-1 : ℤ) ^ (n / UniqueFactorizationMonoid.radical n)

open UniqueFactorizationMonoid

private theorem power_dvd_iff (n k : ℕ) (hn : 0 < n) :
    n ∣ k ^ n ↔ radical n ∣ k := by
  constructor
  · intro h
    exact (exists_dvd_pow_iff_radical_dvd (Nat.ne_of_gt hn)).mp ⟨n, h⟩
  · intro h
    exact (Nat.dvd_radical_pow_self (Nat.ne_of_gt hn)).trans (pow_dvd_pow_of_dvd h n)

private theorem quotient_even_iff (n : ℕ) (hn : 0 < n) :
    Even (n / radical n) ↔ 4 ∣ n := by
  let r := radical n
  let q := n / r
  have hmul : r * q = n := Nat.mul_div_cancel' radical_dvd_self
  have hsq : ¬ 4 ∣ r := by
    exact (Nat.squarefree_iff_prime_squarefree.mp (squarefree_radical (a := n))) 2 Nat.prime_two
  have htwo : 2 ∣ r ↔ 2 ∣ n :=
    dvd_radical_iff_of_irreducible (Nat.prime_iff.mp Nat.prime_two).irreducible (Nat.ne_of_gt hn)
  have hrmod := Nat.mod_lt r (by decide : 0 < 4)
  have hqmod := Nat.mod_lt q (by decide : 0 < 4)
  have hnm : n % 4 = (r % 4 * (q % 4)) % 4 := by
    rw [← hmul, Nat.mul_mod]
  change Even q ↔ 4 ∣ n
  rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
  rw [Nat.dvd_iff_mod_eq_zero] at hsq
  simp only [Nat.dvd_iff_mod_eq_zero] at htwo
  have hr2 : r % 2 = (r % 4) % 2 := by
    exact (Nat.mod_mod_of_dvd r (by decide : 2 ∣ 4)).symm
  have hq2 : q % 2 = (q % 4) % 2 := by
    exact (Nat.mod_mod_of_dvd q (by decide : 2 ∣ 4)).symm
  have hn2 : n % 2 = (n % 4) % 2 := by
    exact (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4)).symm
  interval_cases h : r % 4 <;> interval_cases h' : q % 4 <;> norm_num [*] at * <;> omega


private theorem floor_indicator (n k : ℕ) (hn : 0 < n) :
    ⌊(k : ℚ) ^ n / (n : ℚ)⌋ - ⌊((k : ℚ) ^ n - 1) / (n : ℚ)⌋ =
      if n ∣ k ^ n then (1 : ℤ) else 0 := by
  have hd : (0 : ℤ) < n := by exact Int.natCast_pos.mpr hn
  have hA : ⌊(k : ℚ) ^ n / (n : ℚ)⌋ = (k ^ n : ℕ) / (n : ℤ) := by
    rw [← Nat.cast_pow, Rat.floor_natCast_div_natCast]
  have hB : ⌊((k : ℚ) ^ n - 1) / (n : ℚ)⌋ = ((k ^ n : ℕ) - 1 : ℤ) / (n : ℤ) := by
    rw [← Rat.floor_intCast_div_natCast]
    congr 2
    push_cast
    rfl
  rw [hA, hB]
  let t : ℤ := (k ^ n : ℕ)
  have hrem := Int.emod_nonneg t (ne_of_gt hd)
  have hlt := Int.emod_lt_of_pos t hd
  have heq := Int.mul_ediv_add_emod t (n : ℤ)
  by_cases h : n ∣ k ^ n
  · rw [ite_eq_left h]
    have hz : t % (n : ℤ) = 0 := Int.emod_eq_zero_of_dvd (by dsimp [t]; exact_mod_cast h)
    have hf : (t - 1) / (n : ℤ) = t / (n : ℤ) - 1 := by
      apply (Int.ediv_eq_iff_of_pos hd).mpr
      constructor <;> nlinarith
    change t / (n : ℤ) - (t - 1) / (n : ℤ) = 1
    rw [hf]
    ring
  · rw [ite_eq_right h]
    have hz : t % (n : ℤ) ≠ 0 := by
      intro hz
      apply h
      have hv := Int.dvd_of_emod_eq_zero hz
      dsimp [t] at hv
      exact_mod_cast hv
    have hrpos : 1 ≤ t % (n : ℤ) := by omega
    have hf : (t - 1) / (n : ℤ) = t / (n : ℤ) := by
      apply (Int.ediv_eq_iff_of_pos hd).mpr
      constructor <;> nlinarith
    change t / (n : ℤ) - (t - 1) / (n : ℤ) = 0
    rw [hf, sub_self]

private theorem floor_product_eq (n : ℕ) (hn : 0 < n) :
    floorProduct n = (-1 : ℤ) ^ (n / radical n) := by
  classical
  have hi : Finset.Icc 1 n = Finset.Ioc 0 n := by exact Finset.val_inj.mp rfl
  have hf : floorProduct n = ∏ k ∈ Finset.Ioc 0 n,
      (if radical n ∣ k then (-1 : ℤ) else 1) := by
    unfold floorProduct
    rw [hi]
    apply Finset.prod_congr rfl
    intro k hk
    rw [floor_indicator n k hn]
    simp only [power_dvd_iff n k hn]
    split_ifs <;> norm_num
  rw [hf, ← Finset.prod_filter]
  simp only [Finset.prod_const, Nat.Ioc_filter_dvd_card_eq_div]


open Polynomial Polynomial.Chebyshev

private noncomputable def primitive (n : ℕ) : ℚ[X] :=
  (1 / (2 * ((n : ℚ) + 2))) • T ℚ ((n : ℤ) + 2) -
    (1 / (2 * (n : ℚ))) • T ℚ (n : ℤ)

private theorem primitive_derivative (n : ℕ) (hn : 0 < n) :
    derivative (primitive n) = T ℚ ((n : ℤ) + 1) := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnq2 : (n : ℚ) + 2 ≠ 0 := by positivity
  have hU := two_mul_T_eq_U_sub_U ℚ ((n : ℤ) - 1)
  have he : (n : ℤ) - 1 + 2 = (n : ℤ) + 1 := by omega
  rw [he] at hU
  unfold primitive
  simp only [derivative_sub, derivative_smul, T_derivative_eq_U]
  simp only [smul_eq_C_mul]
  push_cast
  simp only [← mul_assoc]
  have hc1 : (1 / (2 * ((n : ℚ) + 2))) * ((n : ℚ) + 2) = 1 / 2 := by
    field_simp
  have hc2 : (1 / (2 * (n : ℚ))) * (n : ℚ) = 1 / 2 := by
    field_simp
  have castn : (n : ℚ[X]) = C (n : ℚ) := by exact Polynomial.coeff_inj.mp rfl
  have castn2 : (n : ℚ[X]) + 2 = C ((n : ℚ) + 2) := by simp [Polynomial.C_ofNat]
  rw [castn2, castn, ← Polynomial.C_mul, ← Polynomial.C_mul, hc1, hc2]
  rw [show (n : ℤ) + 2 - 1 = (n : ℤ) + 1 by omega]
  have hhalf : C (1 / 2 : ℚ) * (2 : ℚ[X]) = 1 := by
    rw [← Polynomial.C_ofNat 2, ← Polynomial.C_mul]
    norm_num
  calc
    C (1 / 2 : ℚ) * U ℚ ((n : ℤ) + 1) - C (1 / 2 : ℚ) * U ℚ ((n : ℤ) - 1) =
        C (1 / 2 : ℚ) * (U ℚ ((n : ℤ) + 1) - U ℚ ((n : ℤ) - 1)) := by ring
    _ = C (1 / 2 : ℚ) * (2 * T ℚ ((n : ℤ) + 1)) := by rw [← hU]
    _ = T ℚ ((n : ℤ) + 1) := by rw [← mul_assoc, hhalf, one_mul]

private theorem primitive_degree (n : ℕ) : (primitive n).natDegree ≤ n + 2 := by
  unfold primitive
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_smul_le _ _).trans (by
      rw [natDegree_T, show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
      exact le_rfl)
  · exact (natDegree_smul_le _ _).trans (by rw [natDegree_T]; simp only [Int.natAbs_natCast]; omega)

private theorem row_sum_primitive (n : ℕ) (hn : 0 < n) :
    rowSum (n + 1) = (primitive n).eval 1 - (primitive n).eval 0 := by
  have hd := primitive_derivative n hn
  have heval := (primitive n).eval_eq_sum_range' (n := n + 3)
    (by have := primitive_degree n; omega) 1
  simp only [one_pow, mul_one] at heval
  have hs : rowSum (n + 1) = ∑ j ∈ Finset.Icc 1 (n + 2), (primitive n).coeff j := by
    unfold rowSum
    apply Finset.sum_congr (by congr 1)
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by omega, ← hd, coeff_derivative]
    rw [Nat.sub_add_cancel hj1]
    rw [show ((j - 1 : ℕ) : ℚ) + 1 = (j : ℚ) by rw [Nat.cast_sub hj1]; norm_num]
    exact mul_div_cancel_right₀ _ hj0
  rw [hs]
  have hi : Finset.Icc 1 (n + 2) = Finset.Ico 1 (n + 3) := by exact Finset.val_inj.mp rfl
  rw [hi, Finset.sum_Ico_eq_sub _ (by omega)]
  simp only [Finset.sum_range_one, ← heval, coeff_zero_eq_eval_zero]


private theorem cheb_zero_nat (n : ℕ) :
    (T ℚ (n : ℤ)).eval 0 =
      if n % 4 = 0 then 1 else if n % 4 = 2 then -1 else 0 := by
  have hlt := Nat.mod_lt n (by decide : 0 < 4)
  interval_cases h : n % 4
  · have he : Even (n : ℤ) := ⟨(n : ℤ) / 2, by omega⟩
    have he2 : Even ((n : ℤ) / 2) := ⟨(n : ℤ) / 4, by omega⟩
    simp [he, Int.negOnePow_even _ he2]
  · have he : ¬ Even (n : ℤ) := by rintro ⟨k, hk⟩; omega
    simp [T_eval_zero, he]
  · have he : Even (n : ℤ) := ⟨(n : ℤ) / 2, by omega⟩
    have he2 : Odd ((n : ℤ) / 2) := ⟨(n : ℤ) / 4, by omega⟩
    simp [he, Int.negOnePow_odd _ he2]
  · have he : ¬ Even (n : ℤ) := by rintro ⟨k, hk⟩; omega
    simp [T_eval_zero, he]

private theorem row_sum_evaluation (n : ℕ) (hn : 0 < n) :
    rowSum (n + 1) =
      if n % 4 = 0 then 1 / ((n : ℚ) + 2)
      else if n % 4 = 2 then -1 / (n : ℚ)
      else -1 / ((n : ℚ) * ((n : ℚ) + 2)) := by
  rw [row_sum_primitive n hn]
  have hz1 := cheb_zero_nat n
  have hz2 := cheb_zero_nat (n + 2)
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnq2 : (n : ℚ) + 2 ≠ 0 := by positivity
  unfold primitive
  simp only [smul_eq_C_mul, eval_sub, eval_mul, eval_C, T_eval_one, mul_one]
  rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega, hz1, hz2]
  have hlt := Nat.mod_lt n (by decide : 0 < 4)
  interval_cases h : n % 4 <;>
    have h2 : (n + 2) % 4 = (n % 4 + 2) % 4 := by exact (Nat.mod_add_mod n 4 2).symm
  all_goals simp only [h, h2] at *
  all_goals norm_num
  all_goals field_simp
  all_goals ring

private theorem numerator_eq (n : ℕ) (hn : 0 < n) :
    a (n + 1) = if 4 ∣ n then 1 else -1 := by
  unfold a
  rw [row_sum_evaluation n hn]
  have hnz : (0 : ℤ) < n := by exact Int.natCast_pos.mpr hn
  have hn2 : (0 : ℤ) < (n : ℤ) + 2 := by exact Int.sign_eq_one_iff_pos.mp rfl
  have hnumpos : (1 / ((n : ℚ) + 2)).num = 1 := by
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat, Int.cast_one] using
      Rat.num_div_eq_of_coprime (a := 1) (b := (n : ℤ) + 2) hn2 (by simp)
  have hnumneg : (-1 / (n : ℚ)).num = -1 := by
    exact Rat.num_div_eq_of_coprime (a := -1) (b := n) hnz (by simp)
  have hnumprod : (-1 / ((n : ℚ) * ((n : ℚ) + 2))).num = -1 := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Int.cast_neg, Int.cast_one] using
      Rat.num_div_eq_of_coprime (a := -1) (b := (n : ℤ) * ((n : ℤ) + 2))
      (mul_pos hnz hn2) (by simp)
  by_cases h0 : n % 4 = 0
  · simp only [Nat.dvd_iff_mod_eq_zero, h0, ite_true]
    exact hnumpos
  · by_cases h2 : n % 4 = 2
    · simp [h2, Nat.dvd_iff_mod_eq_zero, hnumneg]
    · simp [h0, h2, Nat.dvd_iff_mod_eq_zero, hnumprod]



theorem result : claim := by
  intro n hn
  have hp := floor_product_eq n hn
  refine ⟨?_, hp⟩
  rw [hp]
  simpa only [neg_one_pow_eq_ite, quotient_even_iff n hn] using numerator_eq n hn

end D5.S3.ArithSums.BrowneA164660ChebyshevFloorProduct
