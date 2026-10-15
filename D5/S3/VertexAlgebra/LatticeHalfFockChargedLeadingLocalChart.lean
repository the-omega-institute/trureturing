/- GID: D5/S3/VertexAlgebra/LatticeHalfFockChargedLeadingLocalChart
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockChargedLeadingLocalChart
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite native cleared charged products and their square-root chart coefficients. -/

import D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
import D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
import D5.S3.VertexAlgebra.LatticeHalfFockClearedKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedLeadingLocalChart

open LatticeGeneratingFieldLocality
open LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockOrderedProducts
open LatticeHalfFockProductKernel
open LatticeHalfFockBranchClearing
open LatticeHalfFockClearedKernel
open LatticeHalfFockAllStateField
open scoped BigOperators TensorProduct

noncomputable section

def clearedProductTerm (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) (state : ActualTensor D hu)
    (offset : ℕ) : ActualTensor D hu :=
  (((-1 : ℂ) ^ offset) * ((bilinear D left right).natAbs.choose offset : ℂ)) •
    chargedCoefficient D hu left
      (first - 2 * (((bilinear D left right).natAbs - offset : ℕ) : ℤ))
      (chargedCoefficient D hu right (second - 2 * (offset : ℤ)) state)

def clearedProduct (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) : Module.End ℂ (ActualTensor D hu) where
  toFun state := ∑ offset ∈ Finset.range ((bilinear D left right).natAbs + 1),
    clearedProductTerm D hu left right first second state offset
  map_add' firstState secondState := by
    simp only [clearedProductTerm, map_add, smul_add]
    rw [Finset.sum_add_distrib]
  map_smul' scalar state := by
    simp only [clearedProductTerm, map_smul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro offset member
    rw [smul_smul, smul_smul]
    congr 1
    simp only [RingHom.id_apply]
    ring

private theorem tensor_kernel_bounds (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (state : ActualTensor D hu) :
    ∃ firstBound secondBound : ℤ, ∀ first second : ℤ,
      first < firstBound ∨ second < secondBound →
        tensorCommonKernel D hu left right first second state = 0 := by
  induction state using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by intros; simp⟩
  | tmul polynomial vector =>
    obtain ⟨firstBound, secondBound, bound⟩ :=
      common_kernel_rectangular_support D left right polynomial
    refine ⟨firstBound, secondBound, ?_⟩
    intro first second outside
    simp [tensorCommonKernel, TensorProduct.map_tmul, bound first second outside]
  | add firstState secondState firstProof secondProof =>
    obtain ⟨firstLower, firstUpper, firstProof⟩ := firstProof
    obtain ⟨secondLower, secondUpper, secondProof⟩ := secondProof
    refine ⟨min firstLower secondLower, min firstUpper secondUpper, ?_⟩
    intro first second outside
    have firstOutside : first < firstLower ∨ second < firstUpper := by
      rcases outside with outside | outside
      · exact Or.inl (lt_of_lt_of_le outside (min_le_left _ _))
      · exact Or.inr (lt_of_lt_of_le outside (min_le_left _ _))
    have secondOutside : first < secondLower ∨ second < secondUpper := by
      rcases outside with outside | outside
      · exact Or.inl (lt_of_lt_of_le outside (min_le_right _ _))
      · exact Or.inr (lt_of_lt_of_le outside (min_le_right _ _))
    simp [firstProof first second firstOutside, secondProof first second secondOutside]

def tensorCoefficientTerm (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (series : PowerSeries ℂ)
    (first second : ℤ) (state : ActualTensor D hu) (degree : ℕ) : ActualTensor D hu :=
  (PowerSeries.coeff degree series) •
    tensorCommonKernel D hu left right (first + degree) (second - degree) state

private theorem tensor_coefficient_term_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (series : PowerSeries ℂ)
    (first second : ℤ) (state : ActualTensor D hu) :
    Function.HasFiniteSupport (tensorCoefficientTerm D hu left right series first second state) := by
  obtain ⟨firstBound, secondBound, bound⟩ := tensor_kernel_bounds D hu left right state
  apply BddAbove.finite
  refine bddAbove_def.mpr ⟨(second - secondBound).toNat, ?_⟩
  intro degree supported
  by_contra outside
  have zero := bound (first + degree) (second - degree) (Or.inr (by omega))
  exact supported (by simp [tensorCoefficientTerm, zero])

def tensorCoefficientExpansion (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (series : PowerSeries ℂ)
    (first second : ℤ) : Module.End ℂ (ActualTensor D hu) where
  toFun state := ∑ᶠ degree : ℕ,
    tensorCoefficientTerm D hu left right series first second state degree
  map_add' firstState secondState := by
    have terms : tensorCoefficientTerm D hu left right series first second
        (firstState + secondState) = fun degree =>
          tensorCoefficientTerm D hu left right series first second firstState degree +
            tensorCoefficientTerm D hu left right series first second secondState degree := by
      funext degree
      simp [tensorCoefficientTerm, map_add, smul_add]
    rw [terms]
    exact finsum_add_distrib
      (tensor_coefficient_term_finite D hu left right series first second firstState)
      (tensor_coefficient_term_finite D hu left right series first second secondState)
  map_smul' scalar state := by
    have terms : tensorCoefficientTerm D hu left right series first second
        (scalar • state) = fun degree => scalar •
          tensorCoefficientTerm D hu left right series first second state degree := by
      funext degree
      simp [tensorCoefficientTerm, map_smul, smul_smul, mul_comm]
    rw [terms]
    exact (smul_finsum' scalar
      (tensor_coefficient_term_finite D hu left right series first second state)).symm

private theorem tensor_cleared_coefficient_zero (series : PowerSeries ℂ) :
    PowerSeries.coeff 0 ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) * series) =
      PowerSeries.coeff 0 series := by
  simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
  norm_num

private theorem tensor_cleared_coefficient_one (series : PowerSeries ℂ) :
    PowerSeries.coeff 1 ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) * series) =
      PowerSeries.coeff 1 series := by
  simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
  norm_num

private theorem tensor_cleared_coefficient_next (series : PowerSeries ℂ) (degree : ℕ) :
    PowerSeries.coeff (degree + 2) ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) * series) =
      PowerSeries.coeff (degree + 2) series - PowerSeries.coeff degree series := by
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul]

def tensorPhysicalDifference (D : LatticeData) (hu : IsUnit D.G.det) :
    Module.End ℂ (ℤ → ℤ → Module.End ℂ (ActualTensor D hu)) where
  toFun value := fun first second => value (first - 2) second - value first (second - 2)
  map_add' first second := by
    funext left right
    simp only [Pi.add_apply, sub_eq_add_neg]
    abel
  map_smul' scalar value := by
    funext first second
    simp only [Pi.smul_apply, smul_sub, RingHom.id_apply]

private theorem tensor_difference_term_recurrence (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (series : PowerSeries ℂ)
    (first second : ℤ) (state : ActualTensor D hu) (degree : ℕ) :
    tensorCoefficientTerm D hu left right
        ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) * series)
        (first - 2) second state (degree + 2) =
      tensorCoefficientTerm D hu left right series (first - 2) second state (degree + 2) -
        tensorCoefficientTerm D hu left right series first (second - 2) state degree := by
  dsimp only [tensorCoefficientTerm]
  rw [tensor_cleared_coefficient_next, sub_smul]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  have firstShift : first - 2 + ((degree : ℤ) + 2) = first + degree := by omega
  have secondShift : second - ((degree : ℤ) + 2) = second - 2 - degree := by omega
  rw [firstShift, secondShift]

private theorem tensor_split_twice {D : LatticeData} {hu : IsUnit D.G.det}
    (term : ℕ → ActualTensor D hu)
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

theorem tensor_difference_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (series : PowerSeries ℂ) :
    tensorPhysicalDifference D hu
        (tensorCoefficientExpansion D hu left right series) =
      fun first second => tensorCoefficientExpansion D hu left right
        ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) * series) (first - 2) second := by
  funext first second
  apply LinearMap.ext
  intro state
  let firstTerm := tensorCoefficientTerm D hu left right series (first - 2) second state
  let secondTerm := tensorCoefficientTerm D hu left right series first (second - 2) state
  let clearedTerm := tensorCoefficientTerm D hu left right
    ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) * series) (first - 2) second state
  have firstFinite := tensor_coefficient_term_finite D hu left right series
    (first - 2) second state
  have secondFinite := tensor_coefficient_term_finite D hu left right series
    first (second - 2) state
  have clearedFinite := tensor_coefficient_term_finite D hu left right
    ((1 - PowerSeries.X ^ 2 : PowerSeries ℂ) * series) (first - 2) second state
  have firstTailFinite : Function.HasFiniteSupport (fun degree : ℕ => firstTerm (degree + 2)) :=
    firstFinite.fun_comp_of_injective (g := fun degree : ℕ => degree + 2)
      (fun firstDegree secondDegree equality => Nat.add_right_cancel equality)
  have recurrence (degree : ℕ) : clearedTerm (degree + 2) =
      firstTerm (degree + 2) - secondTerm degree :=
    tensor_difference_term_recurrence D hu left right series first second state degree
  have zeroTerm : clearedTerm 0 = firstTerm 0 := by
    dsimp [clearedTerm, firstTerm, tensorCoefficientTerm]
    rw [tensor_cleared_coefficient_zero]
  have oneTerm : clearedTerm 1 = firstTerm 1 := by
    dsimp [clearedTerm, firstTerm, tensorCoefficientTerm]
    rw [tensor_cleared_coefficient_one]
  change ((∑ᶠ degree : ℕ, firstTerm degree) - ∑ᶠ degree : ℕ, secondTerm degree) =
    ∑ᶠ degree : ℕ, clearedTerm degree
  rw [tensor_split_twice firstTerm firstFinite, tensor_split_twice clearedTerm clearedFinite,
    zeroTerm, oneTerm]
  simp_rw [recurrence]
  rw [finsum_sub_distrib firstTailFinite secondFinite]
  abel

theorem cleared_product_term_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) (state : ActualTensor D hu)
    (offset : ℕ) :
    clearedProductTerm D hu left right first second state offset =
      (((-1 : ℂ) ^ offset) * ((bilinear D left right).natAbs.choose offset : ℂ)) •
    ((chargeScalar D left * chargeScalar D right) •
          tensorCoefficientExpansion D hu left right (halfContraction D left right)
            (first - 2 * (((bilinear D left right).natAbs - offset : ℕ) : ℤ) +
              chargeNorm D left)
            (second - 2 * (offset : ℤ) + chargeNorm D right) state) := by
  simp only [clearedProductTerm]
  rw [charged_tensor_ordered_product]
  rfl

def chartBinomial (exponent : ℤ) (degree : ℕ) : ℂ :=
  PowerSeries.coeff degree (PowerSeries.binomialSeries ℂ exponent)

def chartCoefficientValue (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (cover : ℤ) (degree : ℕ) :
    ActualTensor D hu → ActualTensor D hu := fun state => ∑ᶠ exponent : ℤ,
    chartBinomial exponent degree •
      clearedProduct D hu left right exponent (cover - exponent) state

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedLeadingLocalChart
