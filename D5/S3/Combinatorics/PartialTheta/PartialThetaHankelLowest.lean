/- GID: D5/S3/Combinatorics/PartialTheta/PartialThetaHankelLowest
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PartialTheta/PartialThetaHankelLowest
   mirror-E: none(waiver:unique-extremal-permutation-proof)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Fin]
   utility: none
   digest: Squared deviations isolate the unique lowest Hankel permutation and coefficient. -/

import Mathlib.GroupTheory.Perm.Fin
import D5.S3.Combinatorics.PartialTheta.PartialThetaHankelVandermonde

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PartialTheta.PartialThetaHankelLowest

open Polynomial Finset
open PartialThetaHankelDefs

theorem lowest_term (m n : ℕ) :
    (∀ degree < (m + n + 1) * n.choose 2,
      (hankel m (n + m + 1)).coeff degree = 0) ∧
    (hankel m (n + m + 1)).coeff ((m + n + 1) * n.choose 2) =
      (-1) ^ (m + n + 1).choose 2 := by
  classical
  let dimension := n + m + 1
  let weight : Equiv.Perm (Fin dimension) → ℕ :=
    fun permutation => ∑ index : Fin dimension,
      ((index : ℕ) + (permutation index : ℕ) - m).choose 2
  let admissible : Equiv.Perm (Fin dimension) → Prop :=
    fun permutation => ∀ index : Fin dimension, m ≤ (index : ℕ) + (permutation index : ℕ)
  have choose_square : ∀ index : ℕ,
      2 * (index.choose 2 : ℤ) = (index : ℤ) ^ 2 - index := by
    intro index
    induction index with
    | zero => simp
    | succ index induction_hypothesis =>
      rw [Nat.choose_succ_succ' index 1, Nat.choose_one_right]
      norm_num only [Nat.reduceAdd]
      push_cast
      nlinarith
  have sum_indices : ∀ size : ℕ, (∑ index ∈ range size, index) = size.choose 2 := by
    intro size
    induction size with
    | zero => simp
    | succ size induction_hypothesis =>
      rw [sum_range_succ, induction_hypothesis, Nat.choose_succ_succ' size 1,
        Nat.choose_one_right]
      norm_num only [Nat.reduceAdd]
      omega
  have minimal : ∀ permutation : Equiv.Perm (Fin dimension), admissible permutation →
      dimension * n.choose 2 ≤ weight permutation ∧
        (weight permutation = dimension * n.choose 2 → permutation = Fin.revPerm) := by
    intro permutation valid
    let shifted : Fin dimension → ℕ :=
      fun index => (index : ℕ) + (permutation index : ℕ) - m
    have shifted_cast : ∀ index : Fin dimension,
        (shifted index : ℤ) = (index : ℤ) + (permutation index : ℤ) - m := by
      intro index
      simp only [shifted, Nat.cast_sub (valid index), Nat.cast_add]
    have index_total : (∑ index : Fin dimension, (index : ℤ)) = dimension.choose 2 := by
      have total : (∑ index : Fin dimension, (index : ℕ)) = dimension.choose 2 := by
        rw [Fin.sum_univ_eq_sum_range (fun index => index) dimension, sum_indices]
      exact_mod_cast total
    have shifted_total : (∑ index : Fin dimension, (shifted index : ℤ)) = dimension * n := by
      simp_rw [shifted_cast]
      rw [sum_sub_distrib, sum_add_distrib,
        Equiv.sum_comp permutation (fun index : Fin dimension => (index : ℤ)), index_total]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      have squared := choose_square dimension
      dsimp [dimension] at squared ⊢
      nlinarith
    have square_expansion : ∀ index : Fin dimension,
        ((shifted index : ℤ) - n) ^ 2 =
          2 * ((shifted index).choose 2 : ℤ) - (2 * n - 1) * shifted index + n ^ 2 := by
      intro index
      have fact := choose_square (shifted index)
      nlinarith
    have energy :
        (∑ index : Fin dimension, ((shifted index : ℤ) - n) ^ 2) =
          2 * ((weight permutation : ℤ) - dimension * n.choose 2) := by
      simp_rw [square_expansion]
      rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, shifted_total]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      have total_choose : (∑ index : Fin dimension, ((shifted index).choose 2 : ℤ)) =
          weight permutation := by
        simp only [weight, shifted, Nat.cast_sum]
      rw [total_choose]
      have fact := choose_square n
      nlinarith
    have squares_nonnegative :
        0 ≤ ∑ index : Fin dimension, ((shifted index : ℤ) - n) ^ 2 :=
      sum_nonneg (fun index _ => sq_nonneg _)
    refine ⟨?_, ?_⟩
    · have inequality : (dimension * n.choose 2 : ℤ) ≤ weight permutation := by
        nlinarith
      exact_mod_cast inequality
    · intro equality
      have energy_zero : (∑ index : Fin dimension, ((shifted index : ℤ) - n) ^ 2) = 0 := by
        rw [energy, equality]
        push_cast
        ring
      apply Equiv.ext
      intro index
      have term_zero : ((shifted index : ℤ) - n) ^ 2 = 0 :=
        (sum_eq_zero_iff_of_nonneg (fun index _ => sq_nonneg _)).mp energy_zero
          index (mem_univ index)
      have shifted_value : (shifted index : ℤ) = n := by nlinarith
      have shifted_nat : shifted index = n := by exact_mod_cast shifted_value
      apply Fin.ext
      simp only [Fin.revPerm_apply, Fin.val_rev]
      have index_bound := index.isLt
      have perm_bound := (permutation index).isLt
      dsimp [shifted, dimension] at shifted_nat index_bound perm_bound ⊢
      have index_valid := valid index
      omega
  have reversal_valid : admissible (Fin.revPerm : Equiv.Perm (Fin dimension)) := by
    intro index
    simp only [Fin.revPerm_apply, Fin.val_rev]
    have index_bound := index.isLt
    dsimp [dimension] at index_bound ⊢
    omega
  have reversal_weight : weight (Fin.revPerm : Equiv.Perm (Fin dimension)) =
      dimension * n.choose 2 := by
    unfold weight
    have shifted_reversal : ∀ index : Fin dimension,
        (index : ℕ) + ((Fin.revPerm : Equiv.Perm (Fin dimension)) index : ℕ) - m = n := by
      intro index
      simp only [Fin.revPerm_apply, Fin.val_rev]
      have index_bound := index.isLt
      dsimp [dimension] at index_bound ⊢
      omega
    simp only [shifted_reversal, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  have reversal_sign :
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin dimension))) : ℤ) =
        (-1 : ℤ) ^ dimension.choose 2 := by
    have sign_units : (Fin.revPerm : Equiv.Perm (Fin dimension)).sign =
        (-1 : ℤˣ) ^ dimension.choose 2 := by
      rw [Equiv.Perm.sign_eq_prod_prod_Iio]
      have each_interval : ∀ upper : Fin dimension,
          (∏ lower ∈ Iio upper,
            if (Fin.revPerm : Equiv.Perm (Fin dimension)) lower < Fin.revPerm upper
            then (1 : ℤˣ) else -1) = (-1 : ℤˣ) ^ (upper : ℕ) := by
        intro upper
        calc
          _ = ∏ lower ∈ Iio upper, (-1 : ℤˣ) := by
            apply prod_congr rfl
            intro lower lower_mem
            have ordered : lower < upper := mem_Iio.mp lower_mem
            have reversed : upper.rev < lower.rev := Fin.rev_lt_rev.mpr ordered
            exact if_neg (not_lt_of_ge (le_of_lt reversed))
          _ = _ := by simp
      simp_rw [each_interval]
      rw [prod_pow_eq_pow_sum,
        Fin.sum_univ_eq_sum_range (fun index => index) dimension, sum_indices]
    simpa using congrArg (fun unit : ℤˣ => (unit : ℤ)) sign_units
  have term_formula : ∀ permutation : Equiv.Perm (Fin dimension),
      (∏ index : Fin dimension, coeffA (-(m : ℤ) + (permutation index : ℕ) + (index : ℕ))) =
        if admissible permutation then (X : ℤ[X]) ^ weight permutation else 0 := by
    intro permutation
    by_cases valid : admissible permutation
    · rw [if_pos valid]
      have entries : ∀ index : Fin dimension,
          coeffA (-(m : ℤ) + (permutation index : ℕ) + (index : ℕ)) =
            (X : ℤ[X]) ^ ((index : ℕ) + (permutation index : ℕ) - m).choose 2 := by
        intro index
        have index_valid := valid index
        have nonnegative : 0 ≤ -(m : ℤ) + (permutation index : ℕ) + (index : ℕ) := by
          omega
        have cast_identity : -(m : ℤ) + (permutation index : ℕ) + (index : ℕ) =
            ((index : ℕ) + (permutation index : ℕ) - m : ℕ) := by
          rw [Nat.cast_sub index_valid, Nat.cast_add]
          ring
        simp only [coeffA]
        rw [if_pos nonnegative, cast_identity]
        simp only [Int.toNat_natCast]
      simp only [entries, prod_pow_eq_pow_sum, weight]
    · rw [if_neg valid]
      obtain ⟨index, fails⟩ : ∃ index : Fin dimension,
          ¬ m ≤ (index : ℕ) + (permutation index : ℕ) := by
        simpa only [admissible, not_forall] using valid
      apply prod_eq_zero (mem_univ index)
      have negative : ¬ 0 ≤ -(m : ℤ) + (permutation index : ℕ) + (index : ℕ) := by omega
      simp only [coeffA, if_neg negative]
  have coefficient_formula : ∀ degree : ℕ,
      (hankel m dimension).coeff degree =
        ∑ permutation : Equiv.Perm (Fin dimension),
          if admissible permutation ∧ degree = weight permutation
          then ((Equiv.Perm.sign permutation) : ℤ) else 0 := by
    intro degree
    unfold hankel
    rw [Matrix.det_apply']
    simp only [Matrix.of_apply, term_formula, finsetSum_coeff]
    apply sum_congr rfl
    intro permutation _
    by_cases valid : admissible permutation
    · simp [valid, coeff_intCast_mul, coeff_X_pow]
    · simp [valid]
  change (∀ degree < (m + n + 1) * n.choose 2,
      (hankel m dimension).coeff degree = 0) ∧
    (hankel m dimension).coeff ((m + n + 1) * n.choose 2) =
      (-1) ^ (m + n + 1).choose 2
  have dimension_identity : m + n + 1 = dimension := by dsimp [dimension]; omega
  rw [dimension_identity]
  constructor
  · intro degree below
    rw [coefficient_formula]
    apply sum_eq_zero
    intro permutation _
    by_cases valid : admissible permutation
    · have lower_bound := (minimal permutation valid).1
      have unequal : degree ≠ weight permutation := by omega
      simp [unequal]
    · simp [valid]
  · rw [coefficient_formula]
    rw [sum_eq_single (Fin.revPerm : Equiv.Perm (Fin dimension))]
    · simp only [reversal_valid, reversal_weight, and_self, if_true]
      exact reversal_sign
    · intro permutation _ not_reversal
      by_cases valid : admissible permutation
      · have unequal : dimension * n.choose 2 ≠ weight permutation := by
          intro equality
          exact not_reversal ((minimal permutation valid).2 equality.symm)
        simp [unequal]
      · simp [valid]
    · simp


end D5.S3.Combinatorics.PartialTheta.PartialThetaHankelLowest
