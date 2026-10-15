/- GID: D5/S3/VertexAlgebra/LatticeHalfFockOriginalTwoSheetChartRecurrence
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockOriginalTwoSheetChartRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native finite charged diagonals and exact two-sheet starting-order vanishing. -/

import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalLocality
import D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.PowerSeries.Order

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockOrderedProducts
open LatticeHalfFockBranchClearing LatticeHalfFockClearedKernel
open LatticeHalfFockPhysicalLocality FieldNormalProductLocality
open scoped BigOperators TensorProduct

noncomputable section

structure NativeLattice where
  lattice : LatticeData
  native : IsUnit lattice.G.det

def clearedOrderedCoefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) : Module.End ℂ (ActualTensor D hu) :=
  ∑ offset ∈ Finset.range ((bilinear D left right).natAbs + 1),
    (((-1 : ℂ) ^ offset) * ((bilinear D left right).natAbs.choose offset : ℂ)) •
      (chargedCoefficient D hu left (first - 2 * ((bilinear D left right).natAbs - offset)) *
        chargedCoefficient D hu right (second - 2 * offset))

private theorem cleared_ordered_difference (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) :
    clearedOrderedCoefficient D hu left right first second =
      ((deltaEnd ^ (bilinear D left right).natAbs)
        (orderedProducts D hu left right first second)) 0 0 := by
  classical
  rw [FieldDeltaBinomial.delta_binomial]
  unfold clearedOrderedCoefficient
  apply Finset.sum_congr rfl
  intro offset member
  simp only [orderedProducts, zero_add]

private theorem cleared_ordered_kernel (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) :
    clearedOrderedCoefficient D hu left right first second =
      (chargeScalar D left * chargeScalar D right) •
        ∑ degree ∈ Finset.range (2 * (bilinear D left right).natAbs + 1),
          (clearedPolynomial (bilinear D left right)).coeff degree •
            tensorCommonKernel D hu left right
              (first + chargeNorm D left - 2 * (bilinear D left right).natAbs + degree)
              (second + chargeNorm D right - degree) := by
  classical
  apply TensorProduct.ext'
  intro polynomial vector
  rw [cleared_ordered_difference, iterate_products_pure]
  simp only [mul_zero, sub_zero]
  rw [native_cleared_kernel_expansion]
  simp only []
  rw [cleared_polynomial_expansion]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply,
    tensorCommonKernel, TensorProduct.map_tmul, Module.End.mul_apply,
    TensorProduct.sum_tmul, TensorProduct.smul_tmul']

private theorem cleared_ordered_rectangular_support (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (state : ActualTensor D hu) :
    ∃ firstBound secondBound : ℤ, ∀ first second : ℤ,
      first < firstBound ∨ second < secondBound →
        clearedOrderedCoefficient D hu left right first second state = 0 := by
  classical
  obtain ⟨firstBound, secondBound, bound⟩ := tensor_kernel_bounds D hu left right state
  refine ⟨firstBound - chargeNorm D left, secondBound - chargeNorm D right, ?_⟩
  intro first second outside
  rw [cleared_ordered_kernel]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  have zero : (∑ degree ∈ Finset.range (2 * (bilinear D left right).natAbs + 1),
      (clearedPolynomial (bilinear D left right)).coeff degree •
        tensorCommonKernel D hu left right
          (first + chargeNorm D left - 2 * (bilinear D left right).natAbs + degree)
          (second + chargeNorm D right - degree) state) = 0 := by
    apply Finset.sum_eq_zero
    intro degree member
    have degreeBound := Finset.mem_range.mp member
    have outsideKernel :
        first + chargeNorm D left - 2 * (bilinear D left right).natAbs + degree < firstBound ∨
          second + chargeNorm D right - degree < secondBound := by
      rcases outside with outside | outside
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rw [bound _ _ outsideKernel, smul_zero]
  rw [zero, smul_zero]

theorem cleared_diagonal_support (object : NativeLattice)
    (left right : Charge object.lattice) (total : ℤ)
    (state : ActualTensor object.lattice object.native) :
    Function.HasFiniteSupport (fun exponent : ℤ =>
      clearedOrderedCoefficient object.lattice object.native left right
        exponent (total - exponent) state) := by
  rcases object with ⟨D, hu⟩
  classical
  obtain ⟨firstBound, secondBound, bound⟩ :=
    cleared_ordered_rectangular_support D hu left right state
  apply (Set.finite_Icc firstBound (total - secondBound)).subset
  intro exponent nonzero
  change firstBound ≤ exponent ∧ exponent ≤ total - secondBound
  constructor
  · by_contra outside
    exact nonzero (bound exponent (total - exponent) (Or.inl (by omega)))
  · by_contra outside
    exact nonzero (bound exponent (total - exponent) (Or.inr (by omega)))

def halfIntegerBinomial (exponent : ℤ) (order : ℕ) : ℂ :=
  Ring.choose ((exponent : ℂ) / 2) order

private theorem weighted_diagonal_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (total : ℤ) (state : ActualTensor D hu) (weight : ℤ → ℂ) :
    Function.HasFiniteSupport (fun exponent : ℤ => weight exponent •
      clearedOrderedCoefficient D hu left right exponent (total - exponent) state) := by
  apply (cleared_diagonal_support ⟨D, hu⟩ left right total state).subset
  intro exponent nonzero zero
  exact nonzero (by simp [zero])

private def weightedDiagonal (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (total : ℤ) (weight : ℤ → ℂ) :
    Module.End ℂ (ActualTensor D hu) where
  toFun state := ∑ᶠ exponent : ℤ, weight exponent •
    clearedOrderedCoefficient D hu left right exponent (total - exponent) state
  map_add' firstState secondState := by
    simp only [map_add, smul_add]
    exact finsum_add_distrib
      (weighted_diagonal_finite D hu left right total firstState weight)
      (weighted_diagonal_finite D hu left right total secondState weight)
  map_smul' scalar state := by
    simp only [map_smul, RingHom.id_apply]
    simp only [smul_comm (weight _) scalar]
    exact (smul_finsum' scalar
      (weighted_diagonal_finite D hu left right total state weight)).symm

def localPlus (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (order : ℕ) (total : ℤ) : Module.End ℂ (ActualTensor D hu) :=
  weightedDiagonal D hu left right total (fun exponent => halfIntegerBinomial exponent order)

private theorem cleared_ordered_monodromy (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) (state : ActualTensor D hu) :
    clearedOrderedCoefficient D hu (-left) right first second state =
      ((-1 : ℂ) ^ first) • clearedOrderedCoefficient D hu left right first second state := by
  classical
  simp only [clearedOrderedCoefficient, LatticeFiniteNegativeGeneration.bilinear_neg_left,
    Int.natAbs_neg, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro offset member
  rw [LatticeHalfFockChargedMonodromy.charged_coefficient_coordinate_monodromy,
    LinearMap.smul_apply]
  have sign : ((-1 : ℂ) ^
      (first - 2 * (((bilinear D left right).natAbs : ℤ) - offset))) = (-1 : ℂ) ^ first := by
    have evenShift : Even (2 * (((bilinear D left right).natAbs : ℤ) - offset)) :=
      ⟨((bilinear D left right).natAbs : ℤ) - offset, by omega⟩
    rw [zpow_sub₀ (by norm_num), evenShift.neg_one_zpow, div_one]
  rw [sign]
  exact smul_comm _ _ _

private theorem minus_sum_plus_neg (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (order : ℕ) (total : ℤ) (state : ActualTensor D hu) :
    (∑ᶠ exponent : ℤ, (((-1 : ℂ) ^ exponent) * halfIntegerBinomial exponent order) •
      clearedOrderedCoefficient D hu left right exponent (total - exponent) state) =
        localPlus D hu (-left) right order total state := by
  change _ = ∑ᶠ exponent : ℤ, halfIntegerBinomial exponent order •
    clearedOrderedCoefficient D hu (-left) right exponent (total - exponent) state
  apply finsum_congr
  intro exponent
  rw [cleared_ordered_monodromy, mul_smul]
  exact smul_comm _ _ _

def localMinus (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (order : ℕ) (total : ℤ) : Module.End ℂ (ActualTensor D hu) where
  toFun state := ∑ᶠ exponent : ℤ,
    (((-1 : ℂ) ^ exponent) * halfIntegerBinomial exponent order) •
      clearedOrderedCoefficient D hu left right exponent (total - exponent) state
  map_add' firstState secondState := by
    simp only [minus_sum_plus_neg]
    exact map_add (localPlus D hu (-left) right order total) firstState secondState
  map_smul' scalar state := by
    simp only [minus_sum_plus_neg, RingHom.id_apply]
    exact map_smul (localPlus D hu (-left) right order total) scalar state

private theorem binomial_series_nat_multiple (scalar : ℂ) (degree : ℕ) :
    PowerSeries.binomialSeries ℂ ((degree : ℂ) * scalar) =
      (PowerSeries.binomialSeries ℂ scalar) ^ degree := by
  induction degree with
  | zero => simp
  | succ degree inductionProof =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      PowerSeries.binomialSeries_add, inductionProof, pow_succ]

private theorem clearing_weight_vanishes (gram shift : ℤ) (order : ℕ)
    (below : order < 2 * gram.toNat) :
    (∑ degree ∈ Finset.range (2 * gram.natAbs + 1),
      (clearedPolynomial gram).coeff degree *
        halfIntegerBinomial (shift - degree) order) = 0 := by
  classical
  let root := PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ)
  let base := PowerSeries.binomialSeries ℂ ((shift : ℂ) / 2)
  have binomial (degree : ℕ) :
      PowerSeries.binomialSeries ℂ (((shift - degree : ℤ) : ℂ) / 2) =
        base * root ^ degree := by
    have exponent : (((shift - degree : ℤ) : ℂ) / 2) =
        (shift : ℂ) / 2 + (degree : ℂ) * (-1 / 2) := by
      push_cast
      ring
    rw [exponent, PowerSeries.binomialSeries_add, binomial_series_nat_multiple]
  have evaluation :
      (clearedPolynomial gram).eval₂ (PowerSeries.C : ℂ →+* PowerSeries ℂ) root =
        (1 - root) ^ (2 * gram.toNat) * (1 + root) ^ (2 * (-gram).toNat) := by
    simp [clearedPolynomial, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
      Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_X]
  have evaluationSum := Polynomial.eval₂_eq_sum_range'
    (PowerSeries.C : ℂ →+* PowerSeries ℂ)
    (Nat.lt_succ_of_le (cleared_polynomial_degree gram)) root
  have coefficient :
      (∑ degree ∈ Finset.range (2 * gram.natAbs + 1),
        (clearedPolynomial gram).coeff degree * halfIntegerBinomial (shift - degree) order) =
        PowerSeries.coeff order (base *
          ((clearedPolynomial gram).eval₂ (PowerSeries.C : ℂ →+* PowerSeries ℂ) root)) := by
    rw [evaluationSum, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro degree member
    rw [mul_left_comm base, PowerSeries.coeff_C_mul, ← binomial]
    simp [halfIntegerBinomial]
  rw [coefficient, evaluation]
  have constant : PowerSeries.constantCoeff (1 - root) = 0 := by
    simp [root]
  have bound := PowerSeries.le_order_pow_of_constantCoeff_eq_zero
    (2 * gram.toNat) constant
  rw [show base * ((1 - root) ^ (2 * gram.toNat) * (1 + root) ^ (2 * (-gram).toNat)) =
    (base * (1 + root) ^ (2 * (-gram).toNat)) * (1 - root) ^ (2 * gram.toNat) by ring]
  apply PowerSeries.coeff_mul_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast below) bound

private theorem weighted_kernel_diagonal_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (total shift : ℤ) (state : ActualTensor D hu)
    (weight : ℤ → ℂ) :
    Function.HasFiniteSupport (fun exponent : ℤ => weight exponent •
      tensorCommonKernel D hu left right (exponent + shift) (total - (exponent + shift))
        state) := by
  classical
  obtain ⟨firstBound, secondBound, bound⟩ := tensor_kernel_bounds D hu left right state
  apply (Set.finite_Icc (firstBound - shift) (total - secondBound - shift)).subset
  intro exponent nonzero
  change firstBound - shift ≤ exponent ∧ exponent ≤ total - secondBound - shift
  constructor
  · by_contra outside
    exact nonzero (by
      change weight exponent • (tensorCommonKernel D hu left right (exponent + shift)
        (total - (exponent + shift)) state) = 0
      rw [bound _ _ (Or.inl (by omega)), smul_zero])
  · by_contra outside
    exact nonzero (by
      change weight exponent • (tensorCommonKernel D hu left right (exponent + shift)
        (total - (exponent + shift)) state) = 0
      rw [bound _ _ (Or.inr (by omega)), smul_zero])

private theorem local_plus_below (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (order : ℕ) (total : ℤ) (state : ActualTensor D hu)
    (below : order < 2 * (bilinear D left right).toNat) :
    localPlus D hu left right order total state = 0 := by
  classical
  let gram := bilinear D left right
  let firstShift := chargeNorm D left - 2 * (gram.natAbs : ℤ)
  let kernelTotal := total + chargeNorm D left + chargeNorm D right -
    2 * (gram.natAbs : ℤ)
  let polynomial := clearedPolynomial gram
  let degrees := Finset.range (2 * gram.natAbs + 1)
  let term := fun (exponent : ℤ) (degree : ℕ) =>
    (polynomial.coeff degree * halfIntegerBinomial exponent order) •
      tensorCommonKernel D hu left right (exponent + firstShift + degree)
        (kernelTotal - (exponent + firstShift + degree)) state
  have finiteTerm (degree : ℕ) : Function.HasFiniteSupport (fun exponent => term exponent degree) := by
    simpa only [term, add_assoc] using weighted_kernel_diagonal_finite D hu left right
      kernelTotal (firstShift + degree) state
      (fun exponent => polynomial.coeff degree * halfIntegerBinomial exponent order)
  have finiteSum : Function.HasFiniteSupport (fun exponent => ∑ degree ∈ degrees,
      term exponent degree) := by
    apply Function.HasFiniteSupport.sum
    intro degree
    exact finiteTerm degree
  have expansion : localPlus D hu left right order total state =
      (chargeScalar D left * chargeScalar D right) •
        ∑ᶠ exponent : ℤ, ∑ degree ∈ degrees, term exponent degree := by
    change (∑ᶠ exponent : ℤ, halfIntegerBinomial exponent order •
      clearedOrderedCoefficient D hu left right exponent (total - exponent) state) = _
    rw [smul_finsum' _ finiteSum]
    apply finsum_congr
    intro exponent
    rw [cleared_ordered_kernel]
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro degree member
    have firstEq : exponent + chargeNorm D left - 2 * (gram.natAbs : ℤ) + degree =
        exponent + firstShift + degree := by dsimp [firstShift]; omega
    have secondEq : total - exponent + chargeNorm D right - degree =
        kernelTotal - (exponent + firstShift + degree) := by
      dsimp [kernelTotal, firstShift]
      omega
    simp only [term, polynomial, gram] at firstEq secondEq ⊢
    rw [firstEq, secondEq]
    simp only [LinearMap.smul_apply, smul_smul]
    congr 1
    ring
  rw [expansion, finsum_sum_comm degrees term (fun degree member => finiteTerm degree)]
  have reindex (degree : ℕ) :
      (∑ᶠ exponent : ℤ, term exponent degree) =
        ∑ᶠ exponent : ℤ,
          (polynomial.coeff degree *
            halfIntegerBinomial (exponent - firstShift - degree) order) •
            tensorCommonKernel D hu left right exponent (kernelTotal - exponent) state := by
    let changeVariable : ℤ ≃ ℤ := Equiv.addRight (firstShift + degree)
    apply finsum_eq_of_bijective changeVariable changeVariable.bijective
    intro exponent
    change (polynomial.coeff degree * halfIntegerBinomial exponent order) •
      (tensorCommonKernel D hu left right (exponent + firstShift + degree)
        (kernelTotal - (exponent + firstShift + degree)) state) =
      (polynomial.coeff degree * halfIntegerBinomial
        (exponent + (firstShift + degree) - firstShift - degree) order) •
      (tensorCommonKernel D hu left right (exponent + (firstShift + degree))
        (kernelTotal - (exponent + (firstShift + degree))) state)
    rw [show exponent + (firstShift + degree) - firstShift - degree = exponent by omega]
    simp only [add_assoc]
  simp_rw [reindex]
  have finiteReindexed (degree : ℕ) : Function.HasFiniteSupport (fun exponent : ℤ =>
      (polynomial.coeff degree * halfIntegerBinomial (exponent - firstShift - degree) order) •
        tensorCommonKernel D hu left right exponent (kernelTotal - exponent) state) := by
    simpa only [add_zero] using weighted_kernel_diagonal_finite D hu left right
      kernelTotal 0 state (fun exponent => polynomial.coeff degree *
        halfIntegerBinomial (exponent - firstShift - degree) order)
  rw [sum_finsum_comm degrees _ (fun degree member => finiteReindexed degree)]
  have zero : (∑ᶠ exponent : ℤ, ∑ degree ∈ degrees,
      (polynomial.coeff degree * halfIntegerBinomial (exponent - firstShift - degree) order) •
        tensorCommonKernel D hu left right exponent (kernelTotal - exponent) state) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro exponent
    rw [← Finset.sum_smul]
    have scalar := clearing_weight_vanishes gram (exponent - firstShift) order below
    rw [scalar, zero_smul]
  rw [zero, smul_zero]

theorem local_charts_below_start (object : NativeLattice)
    (left right : Charge object.lattice) (order : ℕ) (total : ℤ)
    (state : ActualTensor object.lattice object.native) :
    (order < ((bilinear object.lattice left right).natAbs +
        bilinear object.lattice left right : ℤ).toNat →
      localPlus object.lattice object.native left right order total state = 0) ∧
    (order < ((bilinear object.lattice left right).natAbs -
        bilinear object.lattice left right : ℤ).toNat →
      localMinus object.lattice object.native left right order total state = 0) := by
  rcases object with ⟨D, hu⟩
  have plusStart : ((bilinear D left right).natAbs + bilinear D left right : ℤ).toNat =
      2 * (bilinear D left right).toNat := by omega
  have minusStart : ((bilinear D left right).natAbs - bilinear D left right : ℤ).toNat =
      2 * (-bilinear D left right).toNat := by omega
  constructor
  · intro below
    rw [plusStart] at below
    exact local_plus_below D hu left right order total state below
  · intro below
    rw [minusStart] at below
    change (∑ᶠ exponent : ℤ,
      (((-1 : ℂ) ^ exponent) * halfIntegerBinomial exponent order) •
        clearedOrderedCoefficient D hu left right exponent (total - exponent) state) = 0
    rw [minus_sum_plus_neg]
    apply local_plus_below
    simpa only [LatticeFiniteNegativeGeneration.bilinear_neg_left] using below

end
end D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence
