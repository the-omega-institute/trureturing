/- GID: D5/S3/Combinatorics/PartialTheta/PartialThetaHankelCoalescence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PartialTheta/PartialThetaHankelCoalescence
   mirror-E: none(waiver:staircase-pascal-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.MvPolynomial.Homogeneous]
   utility: none
   digest: Integral coalescence and finite differences evaluate the shifted Hankel quotient. -/

import D5.S3.Combinatorics.PartialTheta.PartialThetaHankelHighest
import D5.S3.Combinatorics.PartialTheta.PartialThetaHankelQuotient
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PartialTheta.PartialThetaHankelCoalescence

open Finset

set_option maxHeartbeats 1200000 in
theorem staircase_det (m n : ℕ) :
    (Matrix.of fun row column : Fin (m + (n + 1)) =>
      if (row : ℕ) < m then
        (if m - (row : ℕ) ≤ column then (1 : ℤ) else 0)
      else ((column : ℕ).choose ((row : ℕ) - m) : ℤ)).det =
        (-1) ^ (m + 1).choose 2 := by
  classical
  have pascal_det : ∀ size : ℕ,
      (Matrix.of fun row column : Fin size => ((m + column).choose (row : ℕ) : ℤ)).det =
        1 := by
    intro size
    induction size with
    | zero => simp
    | succ size induction_hypothesis =>
      let pascal : Matrix (Fin (size + 1)) (Fin (size + 1)) ℤ :=
        Matrix.of fun row column => (m + column).choose (row : ℕ)
      let difference : Matrix (Fin (size + 1)) (Fin (size + 1)) ℤ :=
        Matrix.of fun row column => Fin.cases (if row = 0 then 1 else 0)
          (fun previous => (if row = previous.succ then 1 else 0) -
            (if row = previous.castSucc then 1 else 0)) column
      have difference_upper : difference.IsUpperTriangular := by
        intro row column below
        change difference row column = 0
        revert below
        refine Fin.cases ?_ (fun previous => ?_) column
        · intro below
          have not_zero : row ≠ 0 := by
            intro equal
            subst row
            exact (lt_irrefl _) below
          simp [difference, not_zero]
        · intro below
          have not_next : row ≠ previous.succ := by
            intro equal
            subst row
            exact (lt_irrefl _) below
          have not_previous : row ≠ previous.castSucc := by
            intro equal
            subst row
            have lower : (previous.succ : ℕ) < (previous.castSucc : ℕ) := below
            simp at lower
          simp [difference, not_next, not_previous]
      have difference_det : difference.det = 1 := by
        rw [Matrix.det_of_isUpperTriangular difference_upper]
        apply prod_eq_one
        intro row _
        refine Fin.cases ?_ (fun previous => ?_) row
        · simp [difference]
        · have distinct : previous.succ ≠ previous.castSucc := by
            intro equal
            have values := congrArg Fin.val equal
            simp at values
          simp [difference, distinct]
      have product_zero : ∀ row : Fin (size + 1), (pascal * difference) row 0 =
          pascal row 0 := by
        intro row
        simp [Matrix.mul_apply, difference, mul_ite]
      have product_successor : ∀ row : Fin (size + 1), ∀ column : Fin size,
          (pascal * difference) row column.succ =
            pascal row column.succ - pascal row column.castSucc := by
        intro row column
        simp [Matrix.mul_apply, difference, mul_sub, sum_sub_distrib, mul_ite]
      have product_first : ∀ column : Fin (size + 1),
          (pascal * difference) 0 column = if column = 0 then 1 else 0 := by
        intro column
        refine Fin.cases ?_ (fun previous => ?_) column
        · rw [product_zero]
          simp [pascal]
        · rw [product_successor]
          simp [pascal]
      have residual : (pascal * difference).submatrix Fin.succ Fin.succ =
          Matrix.of (fun row column : Fin size =>
            ((m + column).choose (row : ℕ) : ℤ)) := by
        ext row column
        rw [Matrix.submatrix_apply, product_successor]
        simp only [pascal, Fin.val_succ, Fin.val_castSucc, Matrix.of_apply]
        have recurrence := Nat.choose_succ_succ (m + (column : ℕ)) (row : ℕ)
        rw [show m + ((column : ℕ) + 1) = m + (column : ℕ) + 1 by omega,
          recurrence, Nat.cast_add]
        ring
      have product_det : (pascal * difference).det = 1 := by
        rw [Matrix.det_succ_row_zero, sum_eq_single 0]
        · rw [product_first]
          simp only [if_true, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
          rw [residual]
          exact induction_hypothesis
        · intro column _ distinct
          rw [product_first, if_neg distinct]
          simp
        · simp
      rw [Matrix.det_mul, difference_det, mul_one] at product_det
      exact product_det
  let dimension := m + (n + 1)
  let staircase : Matrix (Fin dimension) (Fin dimension) ℤ := Matrix.of fun row column =>
    if (row : ℕ) < m then (if m - (row : ℕ) ≤ column then 1 else 0)
    else (column : ℕ).choose ((row : ℕ) - m)
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
  let reverse : Equiv.Perm (Fin dimension) :=
    (Fin.revPerm : Equiv.Perm (Fin (m + 1))).extendDomain first_block
  have reverse_values : ∀ index : Fin dimension,
      (reverse index : ℕ) = if (index : ℕ) ≤ m then m - (index : ℕ) else (index : ℕ) := by
    intro index
    by_cases before : (index : ℕ) ≤ m
    · dsimp only [reverse]
      rw [Equiv.Perm.extendDomain_apply_subtype _ first_block before, if_pos before]
      simp [first_block, Fin.revPerm_apply, Fin.val_rev]
    · dsimp only [reverse]
      rw [Equiv.Perm.extendDomain_apply_not_subtype _ first_block before, if_neg before]
  have reverse_sign : ((Equiv.Perm.sign reverse) : ℤ) = (-1) ^ (m + 1).choose 2 := by
    dsimp only [reverse]
    rw [Equiv.Perm.sign_extendDomain]
    have sum_indices : ∀ size : ℕ, (∑ index ∈ range size, index) = size.choose 2 := by
      intro size
      induction size with
      | zero => simp
      | succ size induction_hypothesis =>
        rw [sum_range_succ, induction_hypothesis, Nat.choose_succ_succ' size 1,
          Nat.choose_one_right]
        norm_num only [Nat.reduceAdd]
        omega
    have unit_sign : (Fin.revPerm : Equiv.Perm (Fin (m + 1))).sign =
        (-1 : ℤˣ) ^ (m + 1).choose 2 := by
      rw [Equiv.Perm.sign_eq_prod_prod_Iio]
      have each_interval : ∀ upper : Fin (m + 1),
          (∏ lower ∈ Iio upper,
            if (Fin.revPerm : Equiv.Perm (Fin (m + 1))) lower < Fin.revPerm upper
            then (1 : ℤˣ) else -1) = (-1 : ℤˣ) ^ (upper : ℕ) := by
        intro upper
        calc
          _ = ∏ lower ∈ Iio upper, (-1 : ℤˣ) := by
            apply prod_congr rfl
            intro lower member
            have ordered : lower < upper := mem_Iio.mp member
            have reversed : upper.rev < lower.rev := Fin.rev_lt_rev.mpr ordered
            exact if_neg (not_lt_of_ge (le_of_lt reversed))
          _ = _ := by simp
      simp_rw [each_interval]
      rw [prod_pow_eq_pow_sum,
        Fin.sum_univ_eq_sum_range (fun index => index) (m + 1), sum_indices]
    simpa using congrArg (fun unit : ℤˣ => (unit : ℤ)) unit_sign
  let reversed : Matrix (Fin dimension) (Fin dimension) ℤ := Matrix.of fun row column =>
    if (row : ℕ) ≤ m then (if (row : ℕ) ≤ column then 1 else 0)
    else (column : ℕ).choose ((row : ℕ) - m)
  have reversal : staircase.submatrix reverse id = reversed := by
    ext row column
    change staircase (reverse row) column = reversed row column
    simp only [staircase, reversed, Matrix.of_apply, reverse_values]
    by_cases before : (row : ℕ) ≤ m
    · simp only [if_pos before]
      by_cases first : (row : ℕ) = 0
      · simp [first]
      · have top : m - (row : ℕ) < m := by omega
        rw [if_pos top]
        have value : m - (m - (row : ℕ)) = row := by omega
        rw [value]
    · simp only [if_neg before]
      rw [if_neg (by omega)]
  let difference : Matrix (Fin dimension) (Fin dimension) ℤ := Matrix.of fun row column =>
    (if row = column then 1 else 0) -
      (if (row : ℕ) < m ∧ (column : ℕ) = (row : ℕ) + 1 then 1 else 0)
  have difference_upper : difference.IsUpperTriangular := by
    intro row column below
    change column < row at below
    have distinct : row ≠ column := ne_of_gt below
    have not_next : ¬ ((row : ℕ) < m ∧ (column : ℕ) = (row : ℕ) + 1) := by
      have ordered : (column : ℕ) < row := below
      omega
    simp [difference, distinct, not_next]
  have difference_det : difference.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular difference_upper]
    apply prod_eq_one
    intro row _
    simp [difference]
  have difference_mul : ∀ row column : Fin dimension,
      (difference * reversed) row column =
        if before : (row : ℕ) < m then
          reversed row column - reversed ⟨(row : ℕ) + 1, by dsimp [dimension]; omega⟩ column
        else reversed row column := by
    intro row column
    simp only [Matrix.mul_apply, difference, reversed, Matrix.of_apply,
      sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul]
    by_cases before : (row : ℕ) < m
    · rw [dif_pos before]
      let next : Fin dimension := ⟨(row : ℕ) + 1, by dsimp [dimension]; omega⟩
      have next_identity : ∀ index : Fin dimension,
          ((index : ℕ) = (row : ℕ) + 1) ↔ index = next := by
        intro index
        change (index : ℕ) = (next : ℕ) ↔ index = next
        exact Fin.ext_iff.symm
      simp_rw [ite_and, if_pos before, next_identity]
      simp [next]
      simp only [if_pos before, Fin.le_def, Fin.lt_def, Nat.add_one_le_iff]
    · rw [dif_neg before]
      simp [before]
  let split : Fin m ⊕ Fin (n + 1) ≃ Fin dimension := finSumFinEquiv
  let bottom_left : Matrix (Fin (n + 1)) (Fin m) ℤ := Matrix.of fun row column =>
    (difference * reversed) (split (Sum.inr row)) (split (Sum.inl column))
  let pascal : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
    Matrix.of fun row column => (m + column).choose (row : ℕ)
  have blocks : (difference * reversed).submatrix split split =
      Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℤ) 0 bottom_left pascal := by
    ext row column
    cases row with
    | inl row =>
      cases column with
      | inl column =>
        change (difference * reversed) (Fin.castAdd (n + 1) row)
          (Fin.castAdd (n + 1) column) = (1 : Matrix (Fin m) (Fin m) ℤ) row column
        rw [difference_mul]
        simp only [Fin.val_castAdd]
        rw [dif_pos row.isLt]
        simp only [reversed, Matrix.of_apply, Fin.val_castAdd]
        have before : (row : ℕ) ≤ m := Nat.le_of_lt row.isLt
        have next_before : (row : ℕ) + 1 ≤ m := by omega
        simp only [if_pos before, if_pos next_before]
        by_cases same : row = column
        · subst column
          simp
        · have unequal : (row : ℕ) ≠ column := by exact fun equal => same (Fin.ext equal)
          simp [same]
          split_ifs <;> omega
      | inr column =>
        change (difference * reversed) (Fin.castAdd (n + 1) row) (Fin.natAdd m column) = 0
        rw [difference_mul]
        simp only [Fin.val_castAdd]
        rw [dif_pos row.isLt]
        simp only [reversed, Matrix.of_apply, Fin.val_castAdd, Fin.val_natAdd]
        have before : (row : ℕ) ≤ m := Nat.le_of_lt row.isLt
        have next_before : (row : ℕ) + 1 ≤ m := by omega
        have left : (row : ℕ) ≤ m + (column : ℕ) := by omega
        have right : (row : ℕ) + 1 ≤ m + (column : ℕ) := by omega
        simp [before, next_before, left, right]
    | inr row =>
      cases column with
      | inl column => rfl
      | inr column =>
        change (difference * reversed) (Fin.natAdd m row) (Fin.natAdd m column) =
          pascal row column
        rw [difference_mul]
        simp only [Fin.val_natAdd]
        rw [dif_neg (by omega)]
        simp only [reversed, Fin.val_natAdd, pascal, Matrix.of_apply]
        by_cases zero : (row : ℕ) = 0
        · simp [zero]
        · rw [if_neg (by omega)]
          simp
  have transformed_det : (difference * reversed).det = 1 := by
    have reindexed : (difference * reversed).det =
        ((difference * reversed).submatrix split split).det :=
      (Matrix.det_reindex_self split.symm (difference * reversed)).symm
    rw [reindexed, blocks, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]
    exact pascal_det (n + 1)
  rw [Matrix.det_mul, difference_det, one_mul, ← reversal, Matrix.det_permute,
    reverse_sign] at transformed_det
  simp only [Int.cast_id] at transformed_det
  have square : ((-1 : ℤ) ^ (m + 1).choose 2) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have normalized := congrArg (fun value : ℤ => (-1) ^ (m + 1).choose 2 * value)
    transformed_det
  rw [← mul_assoc, ← pow_two, square, one_mul, mul_one] at normalized
  exact normalized

set_option maxHeartbeats 1600000 in
theorem coalescence (m count : ℕ)
    (top : Fin m → Fin (m + count) → ℤ)
    (divided : MvPolynomial (Fin count) ℤ)
    (division :
      (Matrix.of fun row column : Fin (m + count) =>
        if before : (row : ℕ) < m then
          MvPolynomial.C (top ⟨row, before⟩ column)
        else MvPolynomial.X ⟨(row : ℕ) - m, by omega⟩ ^ (column : ℕ)).det =
          (∏ lower : Fin count, ∏ upper ∈ Ioi lower,
            (MvPolynomial.X upper - MvPolynomial.X lower)) * divided) :
    MvPolynomial.eval (fun _ => 1) divided =
      (Matrix.of fun row column : Fin (m + count) =>
        if before : (row : ℕ) < m then top ⟨row, before⟩ column
        else ((column : ℕ).choose ((row : ℕ) - m) : ℤ)).det := by
  classical
  have separate : ∀ size : ℕ, ∀ degree : Fin size →₀ ℕ, ∀ powers : Fin size → ℕ,
      MvPolynomial.coeff degree
        (∏ index : Fin size, (1 + MvPolynomial.X index :
          MvPolynomial (Fin size) ℤ) ^ powers index) =
            ∏ index : Fin size, ((powers index).choose (degree index) : ℤ) := by
    intro size
    induction size with
    | zero =>
      intro degree powers
      have degree_zero : degree = 0 := by ext index; exact Fin.elim0 index
      simp [degree_zero]
    | succ size induction_hypothesis =>
      intro degree powers
      rw [← Finsupp.cons_tail degree,
        ← MvPolynomial.finSuccEquiv_coeff_coeff degree.tail _ (degree 0)]
      rw [Fin.prod_univ_succ, map_mul, map_pow, map_add, map_one,
        MvPolynomial.finSuccEquiv_X_zero]
      have tail_image :
          MvPolynomial.finSuccEquiv ℤ size
            (∏ index : Fin size, (1 + MvPolynomial.X index.succ) ^ powers index.succ) =
          Polynomial.C (∏ index : Fin size,
            (1 + MvPolynomial.X index) ^ powers index.succ) := by
        simp only [map_prod, map_pow, map_add, map_one, MvPolynomial.finSuccEquiv_X_succ]
      rw [tail_image, Polynomial.coeff_mul_C, Polynomial.coeff_one_add_X_pow,
        ← MvPolynomial.C_eq_coe_nat, MvPolynomial.coeff_C_mul,
        induction_hypothesis, Fin.prod_univ_succ]
      simp only [Finsupp.tail_apply, Finsupp.cons_zero, Finsupp.cons_succ]
  let degree : Fin count →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun index => (index : ℕ))
  let translate : MvPolynomial (Fin count) ℤ →+* MvPolynomial (Fin count) ℤ :=
    MvPolynomial.eval₂Hom MvPolynomial.C (fun index => 1 + MvPolynomial.X index)
  let vandermonde : MvPolynomial (Fin count) ℤ :=
    (Matrix.vandermonde (fun index : Fin count => MvPolynomial.X index)).det
  have degree_apply : ∀ index : Fin count, degree index = (index : ℕ) := by
    intro index
    simp [degree]
  have integer_cast (value : ℤ) :
      (MvPolynomial.C value : MvPolynomial (Fin count) ℤ) = value := by
    simp
  have determinant_sum (size : ℕ) (matrix : Matrix (Fin size) (Fin size)
      (MvPolynomial (Fin count) ℤ)) :
      matrix.det = ∑ permutation : Equiv.Perm (Fin size),
        MvPolynomial.C (Equiv.Perm.sign permutation : ℤ) *
          ∏ row : Fin size, matrix row (permutation row) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    simp only [Matrix.transpose_apply, integer_cast]
  have homogeneous : vandermonde.IsHomogeneous degree.degree := by
    dsimp [vandermonde]
    rw [determinant_sum]
    apply MvPolynomial.IsHomogeneous.sum
    intro permutation _
    change (MvPolynomial.C (Equiv.Perm.sign permutation : ℤ) *
      ∏ index : Fin count, MvPolynomial.X index ^ (permutation index : ℕ)).IsHomogeneous _
    apply MvPolynomial.IsHomogeneous.C_mul
    have perm_sum : (∑ index : Fin count, (permutation index : ℕ)) = degree.degree := by
      rw [Equiv.sum_comp permutation, Finsupp.degree_eq_sum]
      simp only [degree_apply]
    rw [← perm_sum]
    apply MvPolynomial.IsHomogeneous.prod
    intro index _
    exact MvPolynomial.isHomogeneous_X_pow _ _
  have vandermonde_coefficient : MvPolynomial.coeff degree vandermonde = 1 := by
    dsimp [vandermonde]
    rw [determinant_sum, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_C_mul, Matrix.vandermonde,
      Matrix.of_apply, MvPolynomial.coeff_prod_X_pow]
    rw [sum_eq_single (Equiv.refl (Fin count))]
    · have identity_degree : degree = Finsupp.indicator univ
          (fun (index : Fin count) _ => (index : ℕ)) := by
        ext index
        simp [degree_apply]
      simp [identity_degree]
    · intro permutation _ different
      have not_degree : degree ≠
          Finsupp.indicator univ (fun index _ => (permutation index : ℕ)) := by
        intro equal
        apply different
        apply Equiv.ext
        intro index
        apply Fin.ext
        have value := congrArg (fun exponent : Fin count →₀ ℕ => exponent index) equal
        simpa [degree_apply] using value.symm
      simp [not_degree]
    · simp
  have extract : ∀ polynomial : MvPolynomial (Fin count) ℤ,
      MvPolynomial.coeff degree (vandermonde * polynomial) =
        MvPolynomial.coeff 0 polynomial := by
    intro polynomial
    rw [MvPolynomial.coeff_mul, sum_eq_single (degree, 0)]
    · simp [vandermonde_coefficient]
    · intro pair member different
      have addition : pair.1 + pair.2 = degree := mem_antidiagonal.mp member
      by_cases matching : pair.1.degree = degree.degree
      · have zero : pair.2 = 0 := by
          apply (Finsupp.degree_eq_zero_iff pair.2).mp
          have equality := congrArg Finsupp.degree addition
          rw [map_add, matching] at equality
          omega
        have left : pair.1 = degree := by simpa [zero] using addition
        exact False.elim (different (Prod.ext left zero))
      · rw [homogeneous.coeff_eq_zero matching, zero_mul]
    · simp
  have translate_vandermonde : translate vandermonde = vandermonde := by
    dsimp [vandermonde]
    rw [Matrix.det_vandermonde]
    simp [translate, map_prod, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  have constant_translation : MvPolynomial.coeff 0 (translate divided) =
      MvPolynomial.eval (fun _ => 1) divided := by
    change MvPolynomial.constantCoeff (translate divided) = _
    have composition : MvPolynomial.constantCoeff.comp translate =
        MvPolynomial.eval (fun _ : Fin count => (1 : ℤ)) := by
      ext value <;> simp [translate]
    exact DFunLike.congr_fun composition divided
  have translated_identity :
      translate
        (Matrix.of fun row column : Fin (m + count) =>
          if before : (row : ℕ) < m then MvPolynomial.C (top ⟨row, before⟩ column)
          else MvPolynomial.X ⟨(row : ℕ) - m, by omega⟩ ^ (column : ℕ)).det =
        vandermonde * translate divided := by
    rw [division, map_mul, ← Matrix.det_vandermonde]
    rw [translate_vandermonde]
  have determinant_coefficient :
      MvPolynomial.coeff degree
        (translate
          (Matrix.of fun row column : Fin (m + count) =>
            if before : (row : ℕ) < m then MvPolynomial.C (top ⟨row, before⟩ column)
            else MvPolynomial.X ⟨(row : ℕ) - m, by omega⟩ ^ (column : ℕ)).det) =
        (Matrix.of fun row column : Fin (m + count) =>
          if before : (row : ℕ) < m then top ⟨row, before⟩ column
          else ((column : ℕ).choose ((row : ℕ) - m) : ℤ)).det := by
    rw [determinant_sum, map_sum, MvPolynomial.coeff_sum,
      ← Matrix.det_transpose, Matrix.det_apply']
    apply sum_congr rfl
    intro permutation _
    simp only [map_mul, show ∀ value : ℤ, translate (MvPolynomial.C value) =
      MvPolynomial.C value from fun _ => MvPolynomial.eval₂Hom_C _ _ _,
      MvPolynomial.coeff_C_mul, Matrix.transpose_apply, Matrix.of_apply]
    congr 1
    rw [map_prod]
    rw [Fin.prod_univ_add]
    have top_product :
        (∏ row : Fin m, translate
          (if before : (Fin.castAdd count row : ℕ) < m then
            MvPolynomial.C (top ⟨Fin.castAdd count row, before⟩
              (permutation (Fin.castAdd count row)))
          else MvPolynomial.X ⟨(Fin.castAdd count row : ℕ) - m, by omega⟩ ^
            (permutation (Fin.castAdd count row) : ℕ))) =
          MvPolynomial.C
            (∏ row : Fin m, top row (permutation (Fin.castAdd count row))) := by
      rw [map_prod]
      apply prod_congr rfl
      intro row _
      simp [translate, row.isLt]
    rw [top_product, MvPolynomial.coeff_C_mul]
    have bottom_product :
        (∏ row : Fin count, translate
          (if before : (Fin.natAdd m row : ℕ) < m then
            MvPolynomial.C (top ⟨Fin.natAdd m row, before⟩
              (permutation (Fin.natAdd m row)))
          else MvPolynomial.X ⟨(Fin.natAdd m row : ℕ) - m, by omega⟩ ^
            (permutation (Fin.natAdd m row) : ℕ))) =
          ∏ row : Fin count, (1 + MvPolynomial.X row) ^
            (permutation (Fin.natAdd m row) : ℕ) := by
      apply prod_congr rfl
      intro row _
      simp [translate]
    rw [bottom_product, separate]
    rw [Fin.prod_univ_add]
    simp [degree_apply]
  rw [translated_identity, extract, constant_translation] at determinant_coefficient
  exact determinant_coefficient

end D5.S3.Combinatorics.PartialTheta.PartialThetaHankelCoalescence
