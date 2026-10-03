/- GID: D5/S3/Combinatorics/PartialTheta/PartialThetaHankelHighest
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PartialTheta/PartialThetaHankelHighest
   mirror-E: none(waiver:extremal-quotient-data-proof)
   anchors: []
   utility: none
   digest: Improving swaps determine the Hankel quotient's leading and constant coefficients. -/

import D5.S3.Combinatorics.PartialTheta.PartialThetaHankelLowest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PartialTheta.PartialThetaHankelHighest

open Polynomial Finset
open PartialThetaHankelDefs

set_option maxHeartbeats 1600000 in
theorem quotient_data (m n : ℕ) (quotient : ℤ[X])
    (identity : hankel m (n + m + 1) =
      (-1) ^ (m + 1).choose 2 * quotient * X ^ (m * n.choose 2) * hankel 0 (n + 1)) :
    quotient.Monic ∧ quotient.natDegree = m * n * (n + m + 2) / 2 ∧
      quotient.eval 0 = (-1) ^ (m * n) := by
  classical
  have unique_maximum (m n : ℕ) :
      ∃ greedy : Equiv.Perm (Fin (n + m + 1)),
        (∀ index : Fin (n + m + 1),
          (greedy index : ℕ) =
            if (index : ℕ) ≤ m then m - (index : ℕ) else (index : ℕ)) ∧
        let weight : Equiv.Perm (Fin (n + m + 1)) → ℕ := fun permutation =>
          ∑ index : Fin (n + m + 1), ((index : ℕ) + (permutation index : ℕ) - m).choose 2
        ∀ permutation : Equiv.Perm (Fin (n + m + 1)),
          (∀ index : Fin (n + m + 1), m ≤ (index : ℕ) + (permutation index : ℕ)) →
            weight permutation ≤ weight greedy ∧
              (weight permutation = weight greedy → permutation = greedy) := by
    classical
    let dimension := n + m + 1
    let first_block : Fin (m + 1) ≃ {index : Fin dimension // (index : ℕ) ≤ m} :=
      { toFun := fun index => ⟨⟨(index : ℕ), by
          have bound := index.isLt
          dsimp [dimension]
          omega⟩, by
          have bound := index.isLt
          simpa only [Fin.val_mk] using Nat.le_of_lt_succ bound⟩
        invFun := fun index => ⟨(index.1 : ℕ), Nat.lt_succ_of_le index.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let greedy : Equiv.Perm (Fin dimension) :=
      (Fin.revPerm : Equiv.Perm (Fin (m + 1))).extendDomain first_block
    have greedy_values : ∀ index : Fin dimension,
        (greedy index : ℕ) =
          if (index : ℕ) ≤ m then m - (index : ℕ) else (index : ℕ) := by
      intro index
      by_cases first : (index : ℕ) ≤ m
      · dsimp only [greedy]
        rw [Equiv.Perm.extendDomain_apply_subtype _ first_block first, if_pos first]
        simp [first_block, Fin.revPerm_apply, Fin.val_rev]
      · dsimp only [greedy]
        rw [Equiv.Perm.extendDomain_apply_not_subtype _ first_block first, if_neg first]
    refine ⟨greedy, greedy_values, ?_⟩
    dsimp only
    let weight : Equiv.Perm (Fin dimension) → ℕ := fun permutation =>
      ∑ index : Fin dimension, ((index : ℕ) + (permutation index : ℕ) - m).choose 2
    let admissible : Equiv.Perm (Fin dimension) → Prop := fun permutation =>
      ∀ index : Fin dimension, m ≤ (index : ℕ) + (permutation index : ℕ)
    have greedy_valid : admissible greedy := by
      intro index
      rw [greedy_values]
      split_ifs <;> omega
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
    have maximal_unique : ∀ permutation : Equiv.Perm (Fin dimension),
        admissible permutation →
        (∀ candidate : Equiv.Perm (Fin dimension), admissible candidate →
          weight candidate ≤ weight permutation) → permutation = greedy := by
      intro permutation valid maximal
      have agreement_prefix : ∀ rank : ℕ, ∀ bound : rank < dimension,
          permutation ⟨rank, bound⟩ = greedy ⟨rank, bound⟩ := by
        intro rank
        induction rank using Nat.strong_induction_on with
        | h rank induction_hypothesis =>
          intro bound
          let index : Fin dimension := ⟨rank, bound⟩
          by_contra not_greedy
          have distinct_values : (permutation index : ℕ) ≠ (greedy index : ℕ) := by
            intro equality
            exact not_greedy (Fin.ext equality)
          have larger_column : (greedy index : ℕ) < (permutation index : ℕ) := by
            by_cases first_block : rank ≤ m
            · have value := greedy_values index
              have row_valid := valid index
              dsimp [index] at value row_valid distinct_values ⊢
              rw [if_pos first_block] at value
              omega
            · have value : (greedy index : ℕ) = rank := by
                simpa [index, first_block] using greedy_values index
              rw [value]
              by_contra not_larger
              have column_smaller : (permutation index : ℕ) < rank := by omega
              let earlier_rank := if (permutation index : ℕ) ≤ m
                then m - (permutation index : ℕ) else (permutation index : ℕ)
              have earlier_bound : earlier_rank < rank := by
                dsimp [earlier_rank]
                split_ifs <;> omega
              let earlier : Fin dimension := ⟨earlier_rank, earlier_bound.trans bound⟩
              have earlier_value : (greedy earlier : ℕ) = (permutation index : ℕ) := by
                rw [greedy_values]
                dsimp [earlier, earlier_rank]
                split_ifs <;> omega
              have earlier_agrees := induction_hypothesis earlier_rank earlier_bound
                (earlier_bound.trans bound)
              have collision : permutation earlier = permutation index := by
                rw [earlier_agrees]
                exact Fin.ext earlier_value
              have same := congrArg Fin.val (permutation.injective collision)
              dsimp [earlier, index] at same
              omega
          let later : Fin dimension := permutation.symm (greedy index)
          have later_value : permutation later = greedy index := permutation.apply_symm_apply _
          have later_rank : rank < (later : ℕ) := by
            by_contra not_later
            have earlier_or_same : (later : ℕ) < rank ∨ (later : ℕ) = rank := by omega
            rcases earlier_or_same with earlier | same
            · have agrees := induction_hypothesis (later : ℕ) earlier later.isLt
              have collision : greedy later = greedy index := agrees.symm.trans later_value
              have same_index := congrArg Fin.val (greedy.injective collision)
              dsimp [index] at same_index
              omega
            · have same_index : later = index := Fin.ext same
              rw [same_index] at later_value
              exact not_greedy later_value
          have index_ne_later : index ≠ later := by
            intro equality
            have same := congrArg Fin.val equality
            dsimp [index] at same
            omega
          let swapped : Equiv.Perm (Fin dimension) := permutation * Equiv.swap index later
          have swapped_first : swapped index = greedy index := by
            simp [swapped, Equiv.Perm.mul_apply, later_value]
          have swapped_second : swapped later = permutation index := by
            simp [swapped, Equiv.Perm.mul_apply]
          have swapped_other : ∀ row : Fin dimension, row ≠ index → row ≠ later →
              swapped row = permutation row := by
            intro row not_first not_second
            simp only [swapped, Equiv.Perm.mul_apply,
              Equiv.swap_apply_of_ne_of_ne not_first not_second]
          have swapped_valid : admissible swapped := by
            intro row
            by_cases first : row = index
            · subst row
              rw [swapped_first]
              exact greedy_valid index
            · by_cases second : row = later
              · subst row
                rw [swapped_second]
                exact le_trans (valid index) (Nat.add_le_add_right
                  (Nat.le_of_lt (show (index : ℕ) < (later : ℕ) from later_rank)) _)
              · rw [swapped_other row first second]
                exact valid row
          let contribution : Equiv.Perm (Fin dimension) → Fin dimension → ℤ :=
            fun candidate row => (((row : ℕ) + (candidate row : ℕ) - m).choose 2 : ℤ)
          have cast_weight : ∀ candidate : Equiv.Perm (Fin dimension),
              (weight candidate : ℤ) = ∑ row : Fin dimension, contribution candidate row := by
            intro candidate
            simp only [weight, contribution, Nat.cast_sum]
          have contribution_changes : ∀ row : Fin dimension,
              contribution swapped row - contribution permutation row =
                (if row = index then contribution swapped index - contribution permutation index
                  else 0) +
                (if row = later then contribution swapped later - contribution permutation later
                  else 0) := by
            intro row
            by_cases first : row = index
            · subst row
              simp [index_ne_later]
            · by_cases second : row = later
              · subst row
                simp [index_ne_later.symm]
              · simp [contribution, swapped_other row first second, first, second]
          have total_change :
              (weight swapped : ℤ) - weight permutation =
                (contribution swapped index - contribution permutation index) +
                  (contribution swapped later - contribution permutation later) := by
            rw [cast_weight, cast_weight, ← sum_sub_distrib]
            rw [sum_congr rfl (fun row _ => contribution_changes row)]
            rw [sum_add_distrib]
            simp only [sum_ite_eq', mem_univ, ite_true]
          have gain :
              (contribution swapped index - contribution permutation index) +
                (contribution swapped later - contribution permutation later) =
              ((later : ℤ) - (index : ℤ)) *
                ((permutation index : ℤ) - (greedy index : ℤ)) := by
            dsimp [contribution]
            rw [swapped_first, swapped_second, later_value]
            have first_new := choose_square ((index : ℕ) + (greedy index : ℕ) - m)
            have first_old := choose_square ((index : ℕ) + (permutation index : ℕ) - m)
            have second_new := choose_square ((later : ℕ) + (permutation index : ℕ) - m)
            have second_old := choose_square ((later : ℕ) + (greedy index : ℕ) - m)
            have valid_second_new : m ≤ (later : ℕ) + (permutation index : ℕ) := by
              exact le_trans (valid index) (Nat.add_le_add_right
                (Nat.le_of_lt (show (index : ℕ) < (later : ℕ) from later_rank)) _)
            have valid_second_old : m ≤ (later : ℕ) + (greedy index : ℕ) := by
              simpa only [later_value] using valid later
            rw [Nat.cast_sub (greedy_valid index), Nat.cast_add] at first_new
            rw [Nat.cast_sub (valid index), Nat.cast_add] at first_old
            rw [Nat.cast_sub valid_second_new, Nat.cast_add] at second_new
            rw [Nat.cast_sub valid_second_old, Nat.cast_add] at second_old
            nlinarith
          have positive_gain :
              0 < ((later : ℤ) - (index : ℤ)) *
                ((permutation index : ℤ) - (greedy index : ℤ)) := by
            apply mul_pos <;> apply sub_pos.mpr
            · exact_mod_cast later_rank
            · exact_mod_cast larger_column
          have improves : weight permutation < weight swapped := by
            have improves_int : (weight permutation : ℤ) < weight swapped := by
              rw [gain] at total_change
              linarith
            exact_mod_cast improves_int
          have maximal_bound := maximal swapped swapped_valid
          omega
      apply Equiv.ext
      intro index
      exact agreement_prefix (index : ℕ) index.isLt
    let candidates := univ.filter admissible
    have candidates_nonempty : candidates.Nonempty :=
      ⟨greedy, by simp [candidates, greedy_valid]⟩
    obtain ⟨champion, champion_mem, champion_maximal⟩ :=
      exists_max_image candidates weight candidates_nonempty
    have champion_valid : admissible champion := (mem_filter.mp champion_mem).2
    have champion_greedy : champion = greedy := maximal_unique champion champion_valid
      (fun candidate valid => champion_maximal candidate (by simp [candidates, valid]))
    have universal_bound : ∀ candidate : Equiv.Perm (Fin dimension), admissible candidate →
        weight candidate ≤ weight greedy := by
      intro candidate valid
      rw [← champion_greedy]
      exact champion_maximal candidate (by simp [candidates, valid])
    intro permutation valid
    refine ⟨universal_bound permutation valid, ?_⟩
    intro equality
    change weight permutation = weight greedy at equality
    apply maximal_unique permutation valid
    intro candidate candidate_valid
    rw [equality]
    exact universal_bound candidate candidate_valid
  let dimension := n + m + 1
  let weight : Equiv.Perm (Fin dimension) → ℕ := fun permutation =>
    ∑ index : Fin dimension, ((index : ℕ) + (permutation index : ℕ) - m).choose 2
  let admissible : Equiv.Perm (Fin dimension) → Prop := fun permutation =>
    ∀ index : Fin dimension, m ≤ (index : ℕ) + (permutation index : ℕ)
  obtain ⟨greedy, greedy_values, maximum⟩ := unique_maximum m n
  have greedy_valid : admissible greedy := by
    intro index
    rw [greedy_values]
    split_ifs <;> omega
  have choose_square : ∀ index : ℕ, 2 * index.choose 2 + index = index * index := by
    intro index
    induction index with
    | zero => simp
    | succ index induction_hypothesis =>
      rw [Nat.choose_succ_succ' index 1, Nat.choose_one_right]
      norm_num only [Nat.reduceAdd]
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
  have greedy_sign : ((Equiv.Perm.sign greedy) : ℤ) = (-1) ^ (m + 1).choose 2 := by
    have unit_sign : greedy.sign = (-1 : ℤˣ) ^ (m + 1).choose 2 := by
      rw [Equiv.Perm.sign_eq_prod_prod_Iio]
      have each_interval : ∀ upper : Fin dimension,
          (∏ lower ∈ Iio upper, if greedy lower < greedy upper then (1 : ℤˣ) else -1) =
            if (upper : ℕ) ≤ m then (-1 : ℤˣ) ^ (upper : ℕ) else 1 := by
        intro upper
        by_cases before : (upper : ℕ) ≤ m
        · rw [if_pos before]
          calc
            _ = ∏ lower ∈ Iio upper, (-1 : ℤˣ) := by
              apply prod_congr rfl
              intro lower member
              have ordered : (lower : ℕ) < upper := (mem_Iio.mp member : lower < upper)
              have lower_before : (lower : ℕ) ≤ m := by omega
              have reversed : ¬ greedy lower < greedy upper := by
                rw [Fin.lt_def, greedy_values, greedy_values,
                  if_pos lower_before, if_pos before]
                omega
              rw [if_neg reversed]
            _ = _ := by simp
        · rw [if_neg before]
          apply prod_eq_one
          intro lower member
          have ordered : (lower : ℕ) < upper := (mem_Iio.mp member : lower < upper)
          have increasing : greedy lower < greedy upper := by
            rw [Fin.lt_def, greedy_values, greedy_values, if_neg before]
            split_ifs <;> omega
          exact if_pos increasing
      change (∏ upper : Fin dimension, ∏ lower ∈ Iio upper,
        if greedy lower < greedy upper then (1 : ℤˣ) else -1) = _
      simp_rw [each_interval]
      rw [Fin.prod_univ_eq_prod_range
        (fun index => if index ≤ m then (-1 : ℤˣ) ^ index else 1) dimension]
      rw [show dimension = (m + 1) + n by dsimp [dimension]; omega, prod_range_add]
      have initial : (∏ index ∈ range (m + 1),
          if index ≤ m then (-1 : ℤˣ) ^ index else 1) = (-1 : ℤˣ) ^ (m + 1).choose 2 := by
        calc
          _ = ∏ index ∈ range (m + 1), (-1 : ℤˣ) ^ index := by
            apply prod_congr rfl
            intro index member
            rw [if_pos (by have bound := mem_range.mp member; omega)]
          _ = _ := by rw [prod_pow_eq_pow_sum, sum_indices]
      rw [initial]
      have tail : (∏ index ∈ range n,
          if m + 1 + index ≤ m then (-1 : ℤˣ) ^ (m + 1 + index) else 1) = 1 := by
        apply prod_eq_one
        intro index _
        exact if_neg (by omega)
      rw [tail, mul_one]
    simpa using congrArg (fun unit : ℤˣ => (unit : ℤ)) unit_sign
  have term_formula : ∀ permutation : Equiv.Perm (Fin dimension),
      (∏ index : Fin dimension,
        coeffA (-(m : ℤ) + (permutation index : ℕ) + (index : ℕ))) =
        if admissible permutation then (X : ℤ[X]) ^ weight permutation else 0 := by
    intro permutation
    by_cases valid : admissible permutation
    · rw [if_pos valid]
      have entries : ∀ index : Fin dimension,
          coeffA (-(m : ℤ) + (permutation index : ℕ) + (index : ℕ)) =
            (X : ℤ[X]) ^ ((index : ℕ) + (permutation index : ℕ) - m).choose 2 := by
        intro index
        have nonnegative : 0 ≤ -(m : ℤ) + (permutation index : ℕ) + (index : ℕ) := by
          have bound := valid index
          omega
        have shifted : (-(m : ℤ) + (permutation index : ℕ) + (index : ℕ)).toNat =
            (index : ℕ) + (permutation index : ℕ) - m := by omega
        simp only [coeffA, if_pos nonnegative, shifted]
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
  have top_coefficient : (hankel m dimension).coeff (weight greedy) =
      (-1) ^ (m + 1).choose 2 := by
    rw [coefficient_formula, sum_eq_single greedy]
    · simp [greedy_valid, greedy_sign]
    · intro permutation _ distinct
      by_cases valid : admissible permutation
      · have unequal : weight greedy ≠ weight permutation := by
          intro equality
          exact distinct ((maximum permutation valid).2 equality.symm)
        simp [unequal]
      · simp [valid]
    · simp
  have degree_bound : (hankel m dimension).natDegree ≤ weight greedy := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro degree above
    rw [coefficient_formula]
    apply sum_eq_zero
    intro permutation _
    by_cases valid : admissible permutation
    · have bound := (maximum permutation valid).1
      change weight permutation ≤ weight greedy at bound
      have unequal : degree ≠ weight permutation := by omega
      simp [unequal]
    · simp [valid]
  have top_nonzero : (hankel m dimension).coeff (weight greedy) ≠ 0 := by
    rw [top_coefficient]
    exact pow_ne_zero _ (by norm_num)
  have determinant_nonzero : hankel m dimension ≠ 0 := by
    intro zero
    exact top_nonzero (by rw [zero, coeff_zero])
  have determinant_degree : (hankel m dimension).natDegree = weight greedy :=
    natDegree_eq_of_le_of_coeff_ne_zero degree_bound top_nonzero
  have determinant_leading : (hankel m dimension).leadingCoeff =
      (-1) ^ (m + 1).choose 2 := by
    rw [leadingCoeff, determinant_degree, top_coefficient]
  have greedy_weight : weight greedy =
      ∑ index ∈ range n, (m + 2 * (index + 1)).choose 2 := by
    dsimp [weight]
    simp_rw [greedy_values]
    rw [Fin.sum_univ_eq_sum_range
      (fun index => (index + (if index ≤ m then m - index else index) - m).choose 2)
        dimension]
    rw [show dimension = (m + 1) + n by dsimp [dimension]; omega, sum_range_add]
    have initial : (∑ index ∈ range (m + 1),
        (index + (if index ≤ m then m - index else index) - m).choose 2) = 0 := by
      apply sum_eq_zero
      intro index member
      have bound : index ≤ m := by have bound := mem_range.mp member; omega
      simp [bound, Nat.add_sub_of_le bound]
    rw [initial, zero_add]
    apply sum_congr rfl
    intro index _
    congr 1
    rw [if_neg (by omega)]
    omega
  have weight_formula : ∀ count : ℕ,
      2 * (∑ index ∈ range count, (m + 2 * (index + 1)).choose 2) =
        2 * (count + m + 1) * count.choose 2 + 2 * (count + 2).choose 3 +
          m * count * (count + m + 2) := by
    intro count
    induction count with
    | zero => simp
    | succ count induction_hypothesis =>
      rw [sum_range_succ]
      have choose_step := Nat.choose_succ_succ' count 1
      have cube_step := Nat.choose_succ_succ' (count + 2) 2
      have choose_two_step := Nat.choose_succ_succ' (count + 1) 1
      rw [Nat.choose_one_right] at choose_step choose_two_step
      norm_num only [Nat.reduceAdd] at choose_step cube_step choose_two_step
      have square := choose_square (m + 2 * (count + 1))
      nlinarith [choose_square count]
  have normalizer_data := PartialThetaHankelVandermonde.unshifted n
  let normalizer : ℤ[X] :=
    ∏ distance ∈ range n, (X ^ (distance + 1) - 1) ^ (n - distance)
  have normalizer_monic : normalizer.Monic := normalizer_data.2.2.1
  have normalizer_degree : normalizer.natDegree = (n + 2).choose 3 := normalizer_data.2.2.2.1
  have normalizer_zero : normalizer.eval 0 = (-1) ^ (n + 1).choose 2 :=
    normalizer_data.2.2.2.2
  have expanded : hankel m dimension =
      (-1) ^ (m + 1).choose 2 * quotient * X ^ (dimension * n.choose 2) * normalizer := by
    rw [normalizer_data.1] at identity
    have exponent : dimension * n.choose 2 =
        m * n.choose 2 + (n + 1) * n.choose 2 := by dsimp [dimension]; ring
    rw [exponent, pow_add]
    convert identity using 1; ring
  have quotient_nonzero : quotient ≠ 0 := by
    intro zero
    apply determinant_nonzero
    rw [expanded, zero]
    simp
  have sign_square : ((-1 : ℤ) ^ (m + 1).choose 2) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have quotient_monic : quotient.Monic := by
    have leading := congrArg leadingCoeff expanded
    rw [determinant_leading, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow, leadingCoeff_neg, leadingCoeff_one, leadingCoeff_X_pow,
      normalizer_monic.leadingCoeff, mul_one, mul_one] at leading
    have normalized := congrArg (fun value : ℤ => (-1) ^ (m + 1).choose 2 * value) leading
    rw [← mul_assoc, ← pow_two, sign_square, one_mul] at normalized
    exact normalized.symm
  have quotient_degree : quotient.natDegree = m * n * (n + m + 2) / 2 := by
    have degrees := congrArg natDegree expanded
    rw [determinant_degree,
      natDegree_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by simp)) quotient_nonzero)
        (pow_ne_zero _ X_ne_zero)) normalizer_monic.ne_zero,
      natDegree_mul (mul_ne_zero (pow_ne_zero _ (by simp)) quotient_nonzero)
        (pow_ne_zero _ X_ne_zero),
      natDegree_mul (pow_ne_zero _ (by simp)) quotient_nonzero,
      natDegree_pow, natDegree_neg, natDegree_one, mul_zero, zero_add,
      natDegree_X_pow, normalizer_degree] at degrees
    have formula := weight_formula n
    rw [← greedy_weight] at formula
    dsimp [dimension] at degrees
    have doubled : 2 * quotient.natDegree = m * n * (n + m + 2) := by
      nlinarith
    omega
  have quotient_zero : quotient.eval 0 = (-1) ^ (m * n) := by
    have lowest := (PartialThetaHankelLowest.lowest_term m n).2
    have coefficient : (hankel m dimension).coeff (dimension * n.choose 2) =
        (-1) ^ (m + 1).choose 2 * quotient.eval 0 * normalizer.eval 0 := by
      rw [expanded]
      have rearranged : (-1 : ℤ[X]) ^ (m + 1).choose 2 * quotient *
          X ^ (dimension * n.choose 2) * normalizer =
          X ^ (dimension * n.choose 2) *
            ((-1) ^ (m + 1).choose 2 * quotient * normalizer) := by ring
      rw [rearranged]
      simpa [mul_coeff_zero, coeff_zero_eq_eval_zero] using
        coeff_X_pow_mul ((-1 : ℤ[X]) ^ (m + 1).choose 2 * quotient * normalizer)
          (dimension * n.choose 2) 0
    rw [normalizer_zero] at coefficient
    have size_choose : (m + n + 1).choose 2 =
        (m + 1).choose 2 + (n + 1).choose 2 + m * n := by
      have square_size := choose_square (m + n + 1)
      have square_m := choose_square (m + 1)
      have square_n := choose_square (n + 1)
      nlinarith
    have dimension_identity : m + n + 1 = dimension := by dsimp [dimension]; omega
    have size_choose_dimension : dimension.choose 2 =
        (m + 1).choose 2 + (n + 1).choose 2 + m * n := by
      rw [← dimension_identity, size_choose]
    rw [dimension_identity] at lowest
    rw [size_choose_dimension, pow_add, pow_add, coefficient] at lowest
    have both_nonzero : (-1 : ℤ) ^ (m + 1).choose 2 * (-1) ^ (n + 1).choose 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))
    apply mul_left_cancel₀ both_nonzero
    convert lowest using 1; ring
  exact ⟨quotient_monic, quotient_degree, quotient_zero⟩

end D5.S3.Combinatorics.PartialTheta.PartialThetaHankelHighest
