/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import D5.S3.VertexAlgebra.BRST.WeightedFreeAlgebraEulerSeries
import D5.S3.VertexAlgebra.Characters.ActualLeechOrbifoldMonsterDenominator

/-! Group the independently proved integral Monster denominator by total degree. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open Finset Finset.HasAntidiagonal PowerSeries WeightedFreeAlgebraEulerSeries
open ActualLeechOrbifoldMonsterDenominator
  (finiteDiagonalProduct integerDiagonalDenominator coeff_finiteDiagonalProduct_int)
/-- The positive imaginary bidegrees at total degree `d`. -/
def monsterImaginaryPairs (d : ℕ) : Finset (ℕ × ℕ) :=
  (antidiagonal d).filter fun x => 0 < x.1 ∧ 0 < x.2

@[simp] theorem mem_monsterImaginaryPairs (d : ℕ) (x : ℕ × ℕ) :
    x ∈ monsterImaginaryPairs d ↔ x.1 + x.2 = d ∧ 0 < x.1 ∧ 0 < x.2 := by
  simp [monsterImaginaryPairs]

/-- The native imaginary root multiplicity in total degree `d`. -/
def monsterNativeImaginaryMultiplicity (d : ℕ) : ℕ :=
  ∑ x ∈ monsterImaginaryPairs d, ActualLeechOrbifoldMonsterDenominator.multiplicity x.1 x.2

@[simp] theorem monsterNativeImaginaryMultiplicity_zero : monsterNativeImaginaryMultiplicity 0 = 0 := by
  unfold monsterNativeImaginaryMultiplicity
  apply sum_eq_zero
  intro x hx
  rw [mem_monsterImaginaryPairs] at hx
  omega

private theorem trunc_factor_eq_one {N d e : ℕ} (hd : N < d) :
    trunc (N + 1) ((1 - (X : PowerSeries ℤ) ^ d) ^ e) = trunc (N + 1) 1 := by
  have hz : trunc (N + 1) ((X : PowerSeries ℤ) ^ d) = 0 := by
    ext j
    rw [coeff_trunc]
    by_cases hj : j < N + 1
    · simp [hj, coeff_X_pow, show j ≠ d by omega]
    · simp [hj]
  rw [← trunc_trunc_pow, map_sub, hz, sub_zero, trunc_trunc_pow, one_pow]

private theorem trunc_prod_replace {ι : Type*} (s : Finset ι) (f g : ι → PowerSeries ℤ) (N : ℕ)
    (h : ∀ x ∈ s, trunc (N + 1) (f x) = trunc (N + 1) (g x)) :
    trunc (N + 1) (∏ x ∈ s, f x) = trunc (N + 1) (∏ x ∈ s, g x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s hnot ih =>
    rw [prod_insert hnot, prod_insert hnot, ← trunc_trunc_mul_trunc, ← trunc_trunc_mul_trunc (g a),
      h a (mem_insert_self _ _), ih (fun x hx => h x (mem_insert_of_mem hx))]

private theorem truncatedEulerDenominator_eq_finiteDiagonalProduct (N : ℕ) :
    trunc (N + 1) (truncatedEulerDenominator ℤ monsterNativeImaginaryMultiplicity N) =
      trunc (N + 1) (finiteDiagonalProduct N ℤ) := by
  classical
  let square := Icc 1 N ×ˢ Icc 1 N
  let degree : ℕ × ℕ → ℕ := fun x => x.1 + x.2
  let factor : ℕ × ℕ → PowerSeries ℤ :=
    fun x => (1 - X ^ degree x) ^ ActualLeechOrbifoldMonsterDenominator.multiplicity x.1 x.2
  let small := square.filter fun x => degree x ≤ N
  have hprod :
      ∏ x ∈ small, factor x = truncatedEulerDenominator ℤ monsterNativeImaginaryMultiplicity N := by
    unfold truncatedEulerDenominator
    rw [Fin.prod_univ_eq_prod_range
      (fun m : ℕ => (1 - (X : PowerSeries ℤ) ^ m) ^ monsterNativeImaginaryMultiplicity m) (N + 1)]
    rw [← Finset.prod_fiberwise_of_maps_to (g := degree) (s := small) (t := range (N + 1))
      (fun x hx => mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hx).2)) factor]
    apply prod_congr rfl
    intro d hd
    have hfilter : small.filter (fun x => degree x = d) = monsterImaginaryPairs d := by
      ext x
      simp only [small, square, mem_filter, mem_product, mem_Icc, mem_monsterImaginaryPairs, degree]
      have := mem_range.mp hd
      omega
    rw [hfilter, monsterNativeImaginaryMultiplicity, ← Finset.prod_pow_eq_pow_sum]
    apply prod_congr rfl
    intro x hx
    simp [factor, degree, (mem_monsterImaginaryPairs d x).mp hx |>.1]
  rw [← hprod]
  change trunc (N + 1) (∏ x ∈ square.filter (fun x => degree x ≤ N), factor x) =
    trunc (N + 1) (∏ x ∈ square, factor x)
  rw [prod_filter]
  apply trunc_prod_replace
  intro x _
  by_cases hx : degree x ≤ N
  · rw [ite_eq_left hx]
  · rw [ite_eq_right hx]
    exact (trunc_factor_eq_one (Nat.lt_of_not_ge hx)).symm

/-- The finite Euler denominator with summed native imaginary multiplicities. -/
theorem monsterNative_truncatedEulerDenominator_eq_diagonal (N : ℕ) :
    trunc (N + 1) (truncatedEulerDenominator ℤ monsterNativeImaginaryMultiplicity N) =
      trunc (N + 1) integerDiagonalDenominator := by
  rw [truncatedEulerDenominator_eq_finiteDiagonalProduct]
  ext j
  by_cases hj : j < N + 1
  · simpa only [coeff_trunc, ite_eq_left hj] using coeff_finiteDiagonalProduct_int (Nat.le_of_lt_succ hj)
  · simp [coeff_trunc, hj]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
