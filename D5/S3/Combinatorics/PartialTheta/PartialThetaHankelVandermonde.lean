/- GID: D5/S3/Combinatorics/PartialTheta/PartialThetaHankelVandermonde
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PartialTheta/PartialThetaHankelVandermonde
   mirror-E: none(waiver:integral-determinant-proof)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Vandermonde, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Distance multiplicities evaluate the unshifted partial theta Hankel determinant. -/

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic
import D5.S3.Combinatorics.PartialTheta.PartialThetaHankelDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PartialTheta.PartialThetaHankelVandermonde

open Polynomial Finset
open PartialThetaHankelDefs

theorem unshifted (n : ℕ) :
    let normalizer : ℤ[X] :=
      ∏ distance ∈ range n, (X ^ (distance + 1) - 1) ^ (n - distance)
    hankel 0 (n + 1) = X ^ ((n + 1) * n.choose 2) * normalizer ∧
      hankel 0 (n + 1) ≠ 0 ∧ normalizer.Monic ∧
      normalizer.natDegree = (n + 2).choose 3 ∧
      normalizer.eval 0 = (-1) ^ (n + 1).choose 2 := by
  classical
  dsimp only
  have choose_add : ∀ left right : ℕ,
      (left + right).choose 2 = left.choose 2 + right.choose 2 + left * right := by
    intro left right
    induction right with
    | zero => simp
    | succ right induction_hypothesis =>
      rw [Nat.add_succ, Nat.choose_succ_succ, Nat.choose_one_right,
        Nat.choose_succ_succ, Nat.choose_one_right, induction_hypothesis]
      ring
  have sum_indices : ∀ size : ℕ, ∑ index ∈ range size, index = size.choose 2 := by
    intro size
    induction size with
    | zero => simp
    | succ size induction_hypothesis =>
      rw [sum_range_succ, induction_hypothesis, Nat.choose_succ_succ' size 1,
        Nat.choose_one_right]
      norm_num only [Nat.reduceAdd]
      omega
  have sum_choose : ∀ size : ℕ,
      ∑ index ∈ range size, index.choose 2 = size.choose 3 := by
    intro size
    induction size with
    | zero => simp
    | succ size induction_hypothesis =>
      rw [sum_range_succ, induction_hypothesis, Nat.choose_succ_succ' size 2]
      norm_num only [Nat.reduceAdd]
      omega
  have exponent : ∀ size : ℕ, 3 * (size + 1).choose 3 = (size + 1) * size.choose 2 := by
    intro size
    simpa [mul_comm] using (Nat.add_one_mul_choose_eq size 2).symm
  have triangle_product : ∀ size : ℕ,
      (∏ upper ∈ range (size + 1), ∏ lower ∈ range upper,
        ((X : ℤ[X]) ^ upper - X ^ lower)) =
      X ^ (size + 1).choose 3 *
        ∏ distance ∈ range size, (X ^ (distance + 1) - 1) ^ (size - distance) := by
    intro size
    induction size with
    | zero => norm_num [Nat.choose]
    | succ size induction_hypothesis =>
      have last_row :
          (∏ lower ∈ range (size + 1), ((X : ℤ[X]) ^ (size + 1) - X ^ lower)) =
          X ^ (size + 1).choose 2 *
            ∏ distance ∈ range (size + 1), (X ^ (distance + 1) - 1) := by
        calc
          _ = ∏ lower ∈ range (size + 1),
              X ^ lower * (X ^ (size + 1 - lower) - 1) := by
            apply prod_congr rfl
            intro lower lower_mem
            have lower_le : lower ≤ size + 1 := by simpa using le_of_lt (mem_range.mp lower_mem)
            rw [mul_sub, ← pow_add, Nat.add_sub_of_le lower_le, mul_one]
          _ = (∏ lower ∈ range (size + 1), (X : ℤ[X]) ^ lower) *
              ∏ lower ∈ range (size + 1), (X ^ (size + 1 - lower) - 1) :=
            prod_mul_distrib
          _ = X ^ (size + 1).choose 2 *
              ∏ distance ∈ range (size + 1), (X ^ (distance + 1) - 1) := by
            rw [prod_pow_eq_pow_sum, sum_indices]
            congr 1
            calc
              _ = ∏ lower ∈ range (size + 1),
                  ((X : ℤ[X]) ^ (size + 1 - 1 - lower + 1) - 1) := by
                apply prod_congr rfl
                intro lower lower_mem
                have lower_lt := mem_range.mp lower_mem
                congr 2
                omega
              _ = _ := prod_range_reflect (fun distance =>
                (X : ℤ[X]) ^ (distance + 1) - 1) (size + 1)
      have distance_step :
          (∏ distance ∈ range size,
            ((X : ℤ[X]) ^ (distance + 1) - 1) ^ (size - distance)) *
            (∏ distance ∈ range (size + 1), (X ^ (distance + 1) - 1)) =
          ∏ distance ∈ range (size + 1),
            (X ^ (distance + 1) - 1) ^ (size + 1 - distance) := by
        rw [prod_range_succ, prod_range_succ, ← mul_assoc, ← prod_mul_distrib]
        have factors :
            (∏ distance ∈ range size,
              (((X : ℤ[X]) ^ (distance + 1) - 1) ^ (size - distance) *
                (X ^ (distance + 1) - 1))) =
            ∏ distance ∈ range size,
              (X ^ (distance + 1) - 1) ^ (size + 1 - distance) := by
          apply prod_congr rfl
          intro distance distance_mem
          have distance_lt := mem_range.mp distance_mem
          rw [← pow_succ]
          congr 1
          omega
        rw [factors]
        simp
      rw [prod_range_succ, induction_hypothesis, last_row]
      calc
        _ = X ^ ((size + 1).choose 3 + (size + 1).choose 2) *
            ((∏ distance ∈ range size,
              ((X : ℤ[X]) ^ (distance + 1) - 1) ^ (size - distance)) *
              ∏ distance ∈ range (size + 1), (X ^ (distance + 1) - 1)) := by
          rw [pow_add]
          ring
        _ = _ := by
          rw [distance_step, Nat.choose_succ_succ' (size + 1) 2]
          norm_num only [Nat.reduceAdd]
          rw [add_comm]
  have ordered_pairs :
      (∏ lower : Fin (n + 1), ∏ upper ∈ Ioi lower,
        ((X : ℤ[X]) ^ (upper : ℕ) - X ^ (lower : ℕ))) =
      ∏ upper ∈ range (n + 1), ∏ lower ∈ range upper, (X ^ upper - X ^ lower) := by
    have intervals : ∀ upper : Fin (n + 1),
        (∏ lower : Fin (n + 1),
          if lower < upper then ((X : ℤ[X]) ^ (upper : ℕ) - X ^ (lower : ℕ)) else 1) =
        ∏ lower ∈ range (upper : ℕ), (X ^ (upper : ℕ) - X ^ lower) := by
      intro upper
      rw [← prod_filter]
      apply prod_bij (fun (lower : Fin (n + 1)) _ => (lower : ℕ))
      · intro lower lower_mem
        simpa using (mem_filter.mp lower_mem).2
      · intro first _ second _ same
        exact Fin.ext same
      · intro lower lower_mem
        have lower_lt := mem_range.mp lower_mem
        refine ⟨⟨lower, lower_lt.trans upper.isLt⟩, ?_, rfl⟩
        simp only [mem_filter, mem_univ, true_and]
        exact lower_lt
      · intro lower _
        rfl
    have interval_filter : ∀ lower : Fin (n + 1),
        Ioi lower = univ.filter (fun upper => lower < upper) := by
      intro lower
      ext upper
      simp
    simp_rw [interval_filter, prod_filter]
    rw [prod_comm]
    simp_rw [intervals]
    exact Fin.prod_univ_eq_prod_range
      (fun upper => ∏ lower ∈ range upper, ((X : ℤ[X]) ^ upper - X ^ lower)) (n + 1)
  have evaluation : hankel 0 (n + 1) =
      X ^ ((n + 1) * n.choose 2) *
        ∏ distance ∈ range n, (X ^ (distance + 1) - 1) ^ (n - distance) := by
    have entries :
        (Matrix.of fun row column : Fin (n + 1) =>
          coeffA (-(0 : ℤ) + (row : ℕ) + (column : ℕ))) =
        Matrix.of (fun row column : Fin (n + 1) =>
          (X : ℤ[X]) ^ (row : ℕ).choose 2 *
            (X ^ (column : ℕ).choose 2 *
              Matrix.vandermonde (fun index : Fin (n + 1) =>
                (X : ℤ[X]) ^ (index : ℕ)) row column)) := by
      apply Matrix.ext
      intro row column
      simp only [Matrix.of_apply, coeffA, neg_zero, zero_add, ← Int.natCast_add,
        Int.natCast_nonneg, ite_true, Int.toNat_natCast, Matrix.vandermonde_apply]
      rw [choose_add]
      simp [pow_add, pow_mul, mul_assoc]
    unfold hankel
    simp only [Nat.cast_zero]
    rw [entries]
    erw [Matrix.det_mul_column
      (fun row : Fin (n + 1) => (X : ℤ[X]) ^ (row : ℕ).choose 2)
      (Matrix.of fun row column : Fin (n + 1) =>
        (X : ℤ[X]) ^ (column : ℕ).choose 2 *
          Matrix.vandermonde (fun index : Fin (n + 1) =>
            (X : ℤ[X]) ^ (index : ℕ)) row column)]
    erw [Matrix.det_mul_row
      (fun column : Fin (n + 1) => (X : ℤ[X]) ^ (column : ℕ).choose 2)
      (Matrix.vandermonde (fun index : Fin (n + 1) => (X : ℤ[X]) ^ (index : ℕ))),
      Matrix.det_vandermonde]
    rw [ordered_pairs, triangle_product, prod_pow_eq_pow_sum]
    have total : (∑ index : Fin (n + 1), (index : ℕ).choose 2) = (n + 1).choose 3 := by
      rw [Fin.sum_univ_eq_sum_range (fun index => index.choose 2) (n + 1), sum_choose]
    rw [total]
    calc
      _ = (X : ℤ[X]) ^ (3 * (n + 1).choose 3) *
          ∏ distance ∈ range n, (X ^ (distance + 1) - 1) ^ (n - distance) := by
        rw [show 3 * (n + 1).choose 3 =
          (n + 1).choose 3 + ((n + 1).choose 3 + (n + 1).choose 3) by omega,
          pow_add, pow_add]
        ring
      _ = _ := by rw [exponent]
  have monic_factors : ∀ distance : ℕ,
      (((X : ℤ[X]) ^ (distance + 1) - 1) ^ (n - distance)).Monic := by
    intro distance
    have base : ((X : ℤ[X]) ^ (distance + 1) - 1).Monic := by
      simpa using monic_X_pow_sub_C (1 : ℤ) (Nat.succ_ne_zero distance)
    exact base.pow _
  have monicity := monic_prod_of_monic (range n) _ (fun distance _ => monic_factors distance)
  refine ⟨evaluation, ?_, monicity, ?_, ?_⟩
  · rw [evaluation]
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero) monicity.ne_zero
  · rw [natDegree_prod_of_monic _ _ (fun distance _ => monic_factors distance)]
    have sum_degrees : ∀ size : ℕ,
        (∑ distance ∈ range size, (size - distance) * (distance + 1)) =
        (size + 2).choose 3 := by
      intro size
      induction size with
      | zero => simp
      | succ size induction_hypothesis =>
        rw [sum_range_succ]
        have split :
            (∑ distance ∈ range size, (size + 1 - distance) * (distance + 1)) =
            (∑ distance ∈ range size, (size - distance) * (distance + 1)) +
              ∑ distance ∈ range size, (distance + 1) := by
          rw [← sum_add_distrib]
          apply sum_congr rfl
          intro distance distance_mem
          have distance_lt := mem_range.mp distance_mem
          have difference : size + 1 - distance = size - distance + 1 := by omega
          rw [difference]
          ring
        have increments : (∑ distance ∈ range size, (distance + 1)) + (size + 1) =
            (size + 2).choose 2 := by
          rw [sum_add_distrib, sum_indices]
          simp only [sum_const, card_range, smul_eq_mul, mul_one]
          rw [Nat.choose_succ_succ' (size + 1) 1, Nat.choose_one_right,
            Nat.choose_succ_succ' size 1, Nat.choose_one_right]
          norm_num only [Nat.reduceAdd]
          omega
        rw [split, induction_hypothesis]
        simp only [show size + 1 - size = 1 by omega, one_mul]
        rw [add_assoc, increments, Nat.choose_succ_succ' (size + 2) 2]
        norm_num only [Nat.reduceAdd]
        omega
    simp only [natDegree_pow, ← Polynomial.C_1,
      natDegree_X_pow_sub_C]
    exact sum_degrees n
  · have constant_factors : ∀ distance : ℕ,
        ((((X : ℤ[X]) ^ (distance + 1) - 1) ^ (n - distance)).eval 0) =
          (-1 : ℤ) ^ (n - distance) := by
      intro distance
      simp
    simp only [eval_prod, constant_factors]
    rw [prod_pow_eq_pow_sum]
    congr 1
    calc
      _ = ∑ distance ∈ range n, (n - 1 - distance + 1) := by
        apply sum_congr rfl
        intro distance distance_mem
        have distance_lt := mem_range.mp distance_mem
        omega
      _ = ∑ distance ∈ range n, (distance + 1) := sum_range_reflect _ _
      _ = (n + 1).choose 2 := by
        rw [sum_add_distrib, sum_indices]
        simp only [sum_const, card_range, smul_eq_mul, mul_one]
        rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
        norm_num only [Nat.reduceAdd]
        omega

end D5.S3.Combinatorics.PartialTheta.PartialThetaHankelVandermonde
