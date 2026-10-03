/- GID: D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelConfluence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelConfluence
   mirror-E: none(waiver:formal-alternant-confluence)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Vandermonde]
   utility: none
   digest: Distinct coefficient indices determine the first possible alternant coefficient. -/

import Mathlib.LinearAlgebra.Vandermonde
import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelBranches

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelConfluence

open Finset

/-- Confluence is integral: coefficient extraction uses no factorial or discriminant division. -/
theorem alternant_coefficients {R : Type*} [CommRing R] (size : ℕ)
    (f : Fin size → PowerSeries R) (c : Fin size → R) :
    (∀ h : ℕ, h < size.choose 2 →
      PowerSeries.coeff h
        (Matrix.of fun row column => PowerSeries.rescale (c column) (f row)).det = 0) ∧
    PowerSeries.coeff (size.choose 2)
      (Matrix.of fun row column => PowerSeries.rescale (c column) (f row)).det =
        (Matrix.vandermonde c).det *
          (Matrix.of fun row column : Fin size => PowerSeries.coeff column.val (f row)).det := by
  classical
  have index_sum : ∀ n : ℕ, (∑ i : Fin n, i.val) = n.choose 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n previous =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [previous, Nat.choose_succ_succ, Nat.choose_one_right]
      exact Nat.add_comm ..
  have minimum : ∀ n : ℕ, ∀ k : Fin n → ℕ, Function.Injective k →
      n.choose 2 ≤ ∑ i, k i ∧
        ((∑ i, k i) = n.choose 2 → ∀ i, k i < n) := by
    intro n
    induction n with
    | zero => intro k _; simp
    | succ n previous =>
      intro k injective
      have choose_step : (n + 1).choose 2 = n.choose 2 + n := by
        simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ n 1
      have deletion (pivot : Fin (n + 1))
          (positive : ∀ i : Fin n, 0 < k (pivot.succAbove i)) :
          n.choose 2 ≤ ∑ i : Fin n, (k (pivot.succAbove i) - 1) ∧
            ((∑ i : Fin n, (k (pivot.succAbove i) - 1)) = n.choose 2 →
              ∀ i : Fin n, k (pivot.succAbove i) ≤ n) := by
        have smaller_injective : Function.Injective
            (fun i : Fin n => (k (pivot.succAbove i) - 1)) := by
          intro i j equal
          change k (pivot.succAbove i) - 1 = k (pivot.succAbove j) - 1 at equal
          apply Fin.succAbove_right_injective (p := pivot)
          apply injective
          have := positive i
          have := positive j
          omega
        obtain ⟨bound, equal_bound⟩ := previous _ smaller_injective
        refine ⟨bound, ?_⟩
        intro equal i
        have := equal_bound equal i
        have := positive i
        omega
      have total (pivot : Fin (n + 1))
          (positive : ∀ i : Fin n, 0 < k (pivot.succAbove i)) :
          (∑ i : Fin (n + 1), k i) =
            k pivot + (∑ i : Fin n, (k (pivot.succAbove i) - 1)) + n := by
        rw [Fin.sum_univ_succAbove k pivot]
        have shifted : (∑ i : Fin n, k (pivot.succAbove i)) =
            (∑ i : Fin n, (k (pivot.succAbove i) - 1)) + n := by
          calc
            _ = ∑ i : Fin n, (((k (pivot.succAbove i) - 1)) + 1) := by
              apply sum_congr rfl
              intro i _
              have := positive i
              omega
            _ = _ := by simp only [sum_add_distrib, sum_const, card_univ,
                Fintype.card_fin, smul_eq_mul, mul_one]
        rw [shifted]
        omega
      by_cases zero_index : ∃ pivot, k pivot = 0
      · obtain ⟨pivot, at_zero⟩ := zero_index
        have positive (i : Fin n) : 0 < k (pivot.succAbove i) := by
          have distinct := pivot.succAbove_ne i
          have not_zero : k (pivot.succAbove i) ≠ 0 := by
            intro equal
            exact distinct (injective (equal.trans at_zero.symm))
          omega
        obtain ⟨bound, equal_bound⟩ := deletion pivot positive
        have sum_value := total pivot positive
        rw [choose_step]
        constructor
        · omega
        · intro equal i
          by_cases at_pivot : i = pivot
          · rw [at_pivot, at_zero]
            omega
          · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq at_pivot
            have smaller_equal : (∑ i : Fin n, (k (pivot.succAbove i) - 1)) =
                n.choose 2 := by omega
            have := equal_bound smaller_equal j
            omega
      · have positive_all (i : Fin (n + 1)) : 0 < k i := by
          have not_zero : k i ≠ 0 := by
            intro equal
            exact zero_index ⟨i, equal⟩
          omega
        let pivot := Fin.last n
        have positive (i : Fin n) : 0 < k (pivot.succAbove i) := positive_all _
        have bound := (deletion pivot positive).1
        have sum_value := total pivot positive
        have last_positive := positive_all pivot
        rw [choose_step]
        constructor
        · omega
        · intro equal
          omega
  let coefficients (k : Fin size →₀ ℕ) : Matrix (Fin size) (Fin size) R :=
    Matrix.of fun row column => PowerSeries.coeff (k column) (f row)
  let weight (k : Fin size →₀ ℕ) : R := ∏ column, c column ^ k column
  have extraction (h : ℕ) :
      PowerSeries.coeff h
        (Matrix.of fun row column => PowerSeries.rescale (c column) (f row)).det =
      ∑ k ∈ finsuppAntidiag (univ : Finset (Fin size)) h, weight k * (coefficients k).det := by
    rw [Matrix.det_apply', map_sum]
    have sign_coefficient (σ : Equiv.Perm (Fin size)) (F : PowerSeries R) :
        PowerSeries.coeff h ((Equiv.Perm.sign σ : PowerSeries R) * F) =
          (Equiv.Perm.sign σ : R) * PowerSeries.coeff h F := by
      have constant_sign : (Equiv.Perm.sign σ : PowerSeries R) =
          PowerSeries.C (Equiv.Perm.sign σ : R) := by simp
      rw [constant_sign, PowerSeries.coeff_C_mul]
    simp_rw [sign_coefficient, PowerSeries.coeff_prod, Matrix.of_apply,
      PowerSeries.coeff_rescale, prod_mul_distrib, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    simp only [weight, coefficients, Matrix.det_apply', Matrix.of_apply, mul_sum]
    apply sum_congr rfl
    intro σ _
    ring
  have repeated (k : Fin size →₀ ℕ) (not_injective : ¬Function.Injective k) :
      (coefficients k).det = 0 := by
    obtain ⟨i, j, equal, distinct⟩ : ∃ i j, k i = k j ∧ i ≠ j := by
      simpa only [Function.Injective, not_forall, exists_prop] using not_injective
    apply Matrix.det_zero_of_column_eq distinct
    intro row
    simp only [coefficients, Matrix.of_apply, equal]
  constructor
  · intro h below
    rw [extraction]
    apply sum_eq_zero
    intro k member
    rw [repeated, mul_zero]
    intro injective
    have sum_value := (mem_finsuppAntidiag.mp member).1
    change (∑ i : Fin size, k i) = h at sum_value
    have bound := (minimum size k injective).1
    omega
  · let perm_index (σ : Equiv.Perm (Fin size)) : Fin size →₀ ℕ :=
      Finsupp.equivFunOnFinite.symm (fun i => (σ i).val)
    have perm_value (σ : Equiv.Perm (Fin size)) (i : Fin size) :
        perm_index σ i = (σ i).val := by simp [perm_index]
    have perm_injective : Function.Injective perm_index := by
      intro σ τ equal
      apply Equiv.ext
      intro i
      apply Fin.ext
      have entry := congrArg (fun k : Fin size →₀ ℕ => k i) equal
      simpa only [perm_value] using entry
    have perm_member (σ : Equiv.Perm (Fin size)) :
        perm_index σ ∈ finsuppAntidiag (univ : Finset (Fin size)) (size.choose 2) := by
      rw [mem_finsuppAntidiag]
      constructor
      · simp only [perm_value]
        rw [Equiv.sum_comp σ, index_sum]
      · exact subset_univ _
    have represented (k : Fin size →₀ ℕ)
        (member : k ∈ finsuppAntidiag (univ : Finset (Fin size)) (size.choose 2))
        (injective : Function.Injective k) :
        k ∈ univ.image perm_index := by
      have sum_value := (mem_finsuppAntidiag.mp member).1
      have bounds := (minimum size k injective).2 sum_value
      let g : Fin size → Fin size := fun i => ⟨k i, bounds i⟩
      have g_injective : Function.Injective g := by
        intro i j equal
        exact injective (congrArg Fin.val equal)
      let σ := Equiv.ofBijective g ((Finite.injective_iff_bijective).mp g_injective)
      refine mem_image.mpr ⟨σ, mem_univ _, ?_⟩
      ext i
      simp [perm_value, σ, g]
    rw [extraction]
    have reduced :
        (∑ k ∈ finsuppAntidiag (univ : Finset (Fin size)) (size.choose 2),
          weight k * (coefficients k).det) =
        ∑ k ∈ univ.image perm_index, weight k * (coefficients k).det := by
      symm
      apply sum_subset
      · intro k member
        obtain ⟨σ, _, rfl⟩ := mem_image.mp member
        exact perm_member σ
      · intro k member outside
        rw [repeated, mul_zero]
        intro injective
        exact outside (represented k member injective)
    rw [reduced, sum_image perm_injective.injOn]
    have permuted (σ : Equiv.Perm (Fin size)) :
        coefficients (perm_index σ) =
          (Matrix.of fun row column : Fin size =>
            PowerSeries.coeff column.val (f row)).submatrix id σ := by
      ext row column
      simp [coefficients, perm_value]
    simp_rw [permuted, Matrix.det_permute', ← mul_assoc]
    rw [← sum_mul]
    congr 1
    rw [← Matrix.det_transpose, Matrix.det_apply']
    apply sum_congr rfl
    intro σ _
    simp only [weight, perm_value, Matrix.transpose_apply, Matrix.vandermonde_apply]
    ring

end D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelConfluence
