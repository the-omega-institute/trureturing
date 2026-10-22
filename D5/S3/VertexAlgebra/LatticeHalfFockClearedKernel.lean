/- GID: D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockClearedKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Doubled cover differences clear the native supported common-kernel expansion. -/

import D5.S3.VertexAlgebra.LatticeHalfFockProductKernel
import D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing
import D5.S3.VertexAlgebra.BinomialKernelDelta
import Mathlib.Algebra.FiniteSupport.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockClearedKernel

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockProductKernel LatticeHalfFockBranchClearing
open scoped BigOperators

noncomputable section

private def coefficientTerm (D : LatticeData) (left right : Charge D)
    (series : PowerSeries ℂ) (first second : ℤ) (polynomial : Oscillator D)
    (degree : ℕ) : Oscillator D :=
  (PowerSeries.coeff degree series) •
    commonKernel D left right (first + degree) (second - degree) polynomial

private theorem coefficient_term_finite (D : LatticeData) (left right : Charge D)
    (series : PowerSeries ℂ) (first second : ℤ) (polynomial : Oscillator D) :
    Function.HasFiniteSupport (coefficientTerm D left right series first second polynomial) := by
  apply (common_kernel_ordered_finite_support D left right first second polynomial).1.subset
  intro degree supported zero
  exact supported (by simp [coefficientTerm, zero])

def coefficientExpansion (D : LatticeData) (left right : Charge D)
    (series : PowerSeries ℂ) (polynomial : Oscillator D) : ℤ → ℤ → Oscillator D :=
  fun first second => ∑ᶠ degree : ℕ,
    coefficientTerm D left right series first second polynomial degree

private def physicalFirstShift (D : LatticeData) :
    Module.End ℂ (ℤ → ℤ → Oscillator D) where
  toFun distribution := fun first second => distribution (first - 2) second
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def physicalSecondShift (D : LatticeData) :
    Module.End ℂ (ℤ → ℤ → Oscillator D) where
  toFun distribution := fun first second => distribution first (second - 2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def physicalDifference (D : LatticeData) :
    Module.End ℂ (ℤ → ℤ → Oscillator D) :=
  physicalFirstShift D - physicalSecondShift D

private theorem cleared_coefficient_zero (series : PowerSeries ℂ) :
    PowerSeries.coeff 0 ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) * series) =
      PowerSeries.coeff 0 series := by
  simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
  norm_num

private theorem cleared_coefficient_one (series : PowerSeries ℂ) :
    PowerSeries.coeff 1 ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) * series) =
      PowerSeries.coeff 1 series := by
  simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
  norm_num

private theorem cleared_coefficient_next (series : PowerSeries ℂ) (degree : ℕ) :
    PowerSeries.coeff (degree + 2) ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) * series) =
      PowerSeries.coeff (degree + 2) series - PowerSeries.coeff degree series := by
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul]

private theorem difference_term_recurrence (D : LatticeData) (left right : Charge D)
    (series : PowerSeries ℂ) (first second : ℤ) (polynomial : Oscillator D) (degree : ℕ) :
    coefficientTerm D left right ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) * series)
        (first - 2) second polynomial (degree + 2) =
      coefficientTerm D left right series (first - 2) second polynomial (degree + 2) -
        coefficientTerm D left right series first (second - 2) polynomial degree := by
  dsimp only [coefficientTerm]
  rw [cleared_coefficient_next, sub_smul]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  have firstShift : first - 2 + ((degree : ℤ) + 2) = first + degree := by omega
  have secondShift : second - ((degree : ℤ) + 2) = second - 2 - degree := by omega
  rw [firstShift, secondShift]

private theorem split_twice (D : LatticeData) (term : ℕ → Oscillator D)
    (finite : Function.HasFiniteSupport term) :
    (∑ᶠ degree : ℕ, term degree) = term 0 + term 1 +
      (∑ᶠ degree : ℕ, term (degree + 2)) := by
  have onceFinite : Function.HasFiniteSupport (fun degree : ℕ => term (degree + 1)) :=
    finite.fun_comp_of_injective (g := fun degree : ℕ => degree + 1)
      (fun firstDegree secondDegree equality => Nat.add_right_cancel equality)
  rw [BinomialKernelDelta.finsum_split term finite,
    BinomialKernelDelta.finsum_split (fun degree : ℕ => term (degree + 1)) onceFinite]
  simp only [Nat.zero_add, Nat.add_assoc, one_add_one_eq_two]
  abel

theorem physical_difference_expansion (D : LatticeData) (left right : Charge D)
    (series : PowerSeries ℂ) (polynomial : Oscillator D) :
    physicalDifference D (coefficientExpansion D left right series polynomial) =
      fun first second => coefficientExpansion D left right
        ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) * series) polynomial (first - 2) second := by
  funext first second
  let firstTerm := coefficientTerm D left right series (first - 2) second polynomial
  let secondTerm := coefficientTerm D left right series first (second - 2) polynomial
  let clearedTerm := coefficientTerm D left right
    ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) * series) (first - 2) second polynomial
  have firstFinite := coefficient_term_finite D left right series (first - 2) second polynomial
  have secondFinite := coefficient_term_finite D left right series first (second - 2) polynomial
  have clearedFinite := coefficient_term_finite D left right
    ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) * series) (first - 2) second polynomial
  have firstTailFinite : Function.HasFiniteSupport (fun degree : ℕ => firstTerm (degree + 2)) :=
    firstFinite.fun_comp_of_injective (g := fun degree : ℕ => degree + 2)
      (fun firstDegree secondDegree equality =>
      Nat.add_right_cancel equality)
  have recurrence (degree : ℕ) : clearedTerm (degree + 2) =
      firstTerm (degree + 2) - secondTerm degree :=
    difference_term_recurrence D left right series first second polynomial degree
  have zeroTerm : clearedTerm 0 = firstTerm 0 := by
    dsimp [clearedTerm, firstTerm, coefficientTerm]
    rw [cleared_coefficient_zero]
  have oneTerm : clearedTerm 1 = firstTerm 1 := by
    dsimp [clearedTerm, firstTerm, coefficientTerm]
    rw [cleared_coefficient_one]
  change ((∑ᶠ degree : ℕ, firstTerm degree) - ∑ᶠ degree : ℕ, secondTerm degree) =
    ∑ᶠ degree : ℕ, clearedTerm degree
  rw [split_twice D firstTerm firstFinite, split_twice D clearedTerm clearedFinite,
    zeroTerm, oneTerm]
  simp_rw [recurrence]
  rw [finsum_sub_distrib firstTailFinite secondFinite]
  abel

theorem physical_difference_iterate (D : LatticeData) (left right : Charge D)
    (series : PowerSeries ℂ) (polynomial : Oscillator D) (order : ℕ) :
    (physicalDifference D ^ order) (coefficientExpansion D left right series polynomial) =
      fun first second => coefficientExpansion D left right
        ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) ^ order * series) polynomial
          (first - 2 * order) second := by
  induction order with
  | zero => simp [Module.End.one_apply]
  | succ order inductionProof =>
    rw [pow_succ', Module.End.mul_apply, inductionProof]
    funext first second
    have coefficientStep := congrFun (congrFun
      (physical_difference_expansion D left right
        ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) ^ order * series) polynomial)
      (first - 2 * order)) second
    change coefficientExpansion D left right
        ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) ^ order * series) polynomial
        (first - 2 - 2 * order) second -
      coefficientExpansion D left right
        ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) ^ order * series) polynomial
        (first - 2 * order) (second - 2) = _
    have shift : first - 2 - 2 * (order : ℤ) = first - 2 * order - 2 := by omega
    rw [shift]
    change _ = coefficientExpansion D left right
      ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) ^ (order + 1) * series) polynomial
      (first - 2 * ((order + 1 : ℕ) : ℤ)) second
    rw [show first - 2 * ((order + 1 : ℕ) : ℤ) = first - 2 * order - 2 by omega,
      pow_succ' (1 - PowerSeries.X ^ 2 : PowerSeries ℂ) order, mul_assoc]
    exact coefficientStep

theorem native_cleared_kernel_expansion (D : LatticeData) (left right : Charge D)
    (polynomial : Oscillator D) :
    (physicalDifference D ^ (bilinear D left right).natAbs)
        (coefficientExpansion D left right (halfContraction D left right) polynomial) =
      fun first second => coefficientExpansion D left right
        (clearedPolynomial (bilinear D left right)).toPowerSeries polynomial
          (first - 2 * (bilinear D left right).natAbs) second := by
  rw [physical_difference_iterate, half_contraction_physical_clearing]

theorem cleared_polynomial_expansion (D : LatticeData) (left right : Charge D)
    (gram : ℤ) (polynomial : Oscillator D) (first second : ℤ) :
    coefficientExpansion D left right (clearedPolynomial gram).toPowerSeries polynomial
        first second =
      ∑ degree ∈ Finset.range (2 * gram.natAbs + 1),
        (clearedPolynomial gram).coeff degree •
          commonKernel D left right (first + degree) (second - degree) polynomial := by
  classical
  have supported : Function.support
      (coefficientTerm D left right (clearedPolynomial gram).toPowerSeries
        first second polynomial) ⊆ (Finset.range (2 * gram.natAbs + 1) : Set ℕ) := by
    intro degree nonzero
    apply Finset.mem_range.mpr
    by_contra outside
    have zero : (clearedPolynomial gram).coeff degree = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        ((cleared_polynomial_degree gram).trans_lt (by omega))
    exact nonzero (by simp [coefficientTerm, Polynomial.coeff_coe, zero])
  unfold coefficientExpansion
  rw [finsum_eq_sum_of_support_subset _ supported]
  simp only [coefficientTerm, Polynomial.coeff_coe]

private theorem cleared_polynomial_exchange (D : LatticeData) (left right : Charge D)
    (gram : ℤ) (polynomial : Oscillator D) (first second : ℤ) :
    coefficientExpansion D left right (clearedPolynomial gram).toPowerSeries polynomial
        (first - 2 * gram.natAbs) second =
      coefficientExpansion D right left (clearedPolynomial gram).toPowerSeries polynomial
        (second - 2 * gram.natAbs) first := by
  classical
  rw [cleared_polynomial_expansion, cleared_polynomial_expansion]
  rw [← Finset.sum_range_reflect (fun degree =>
    (clearedPolynomial gram).coeff degree •
      commonKernel D right left (second - 2 * gram.natAbs + degree)
        (first - degree) polynomial) (2 * gram.natAbs + 1)]
  apply Finset.sum_congr rfl
  intro degree supported
  have bound : degree ≤ 2 * gram.natAbs := by
    have present := Finset.mem_range.mp supported
    omega
  have subtract : 2 * gram.natAbs + 1 - 1 - degree = 2 * gram.natAbs - degree := by omega
  rw [subtract, cleared_polynomial_coefficient_reciprocity gram degree bound,
    common_kernel_branch_exchange]
  have firstShift : second - 2 * (gram.natAbs : ℤ) +
      ((2 * gram.natAbs - degree : ℕ) : ℤ) = second - degree := by omega
  have secondShift : first - ((2 * gram.natAbs - degree : ℕ) : ℤ) =
      first - 2 * gram.natAbs + degree := by omega
  rw [firstShift, secondShift]

theorem native_cleared_kernel_exchange (D : LatticeData) (left right : Charge D)
    (polynomial : Oscillator D) (first second : ℤ) :
    ((physicalDifference D ^ (bilinear D left right).natAbs)
        (coefficientExpansion D left right (halfContraction D left right) polynomial)) first second =
      ((physicalDifference D ^ (bilinear D left right).natAbs)
        (coefficientExpansion D right left (halfContraction D right left) polynomial)) second first := by
  have firstClearing := congrFun (congrFun
    (native_cleared_kernel_expansion D left right polynomial) first) second
  have secondClearing := congrFun (congrFun
    (native_cleared_kernel_expansion D right left polynomial) second) first
  rw [LatticeFiniteNegativeGeneration.bilinear_symmetric D right left] at secondClearing
  rw [firstClearing, secondClearing]
  exact cleared_polynomial_exchange D left right (bilinear D left right) polynomial first second

end
end D5.S3.VertexAlgebra.LatticeHalfFockClearedKernel
