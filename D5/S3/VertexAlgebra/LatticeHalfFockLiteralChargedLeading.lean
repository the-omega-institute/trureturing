/- GID: D5/S3/VertexAlgebra/LatticeHalfFockLiteralChargedLeading
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockLiteralChargedLeading
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native first coefficients of both original charged square-root charts. -/

import D5.S3.VertexAlgebra.LatticeHalfFockDiagonalFusion
import D5.S3.VertexAlgebra.LatticeHalfFockLiteralLeadingCoefficient
import D5.S3.VertexAlgebra.LatticeHalfFockAllStateField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockLiteralChargedLeading

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockOrderedProducts
open LatticeHalfFockBranchClearing LatticeHalfFockOriginalTwoSheetChartRecurrence
open LatticeHalfFockDiagonalFusion LatticeHalfFockLiteralLeadingCoefficient
open LatticeHalfFockAllStateField
open scoped BigOperators TensorProduct VertexOperator

macro "originalChartSupplier% " supplier:ident : term => do
  let suffix := supplier.getId.toString
  unless suffix ∈ ["cleared_ordered_kernel", "weighted_kernel_diagonal_finite",
      "minus_sum_plus_neg"] do
    Lean.Macro.throwError "unknown original chart supplier"
  let components := ["D5", "S3", "VertexAlgebra", "LatticeHalfFockOriginalTwoSheetChartRecurrence"]
  let privatePrefix := components.foldl Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private")
  let scopedName := components.foldl Lean.Name.str (Lean.Name.num privatePrefix 0)
  return Lean.mkIdent (Lean.Name.str scopedName suffix)

noncomputable section

theorem local_plus_kernel_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (order : ℕ) (total : ℤ) (state : ActualTensor D hu) :
    localPlus D hu left right order total state =
      (chargeScalar D left * chargeScalar D right) •
        ∑ᶠ exponent : ℤ,
          (∑ degree ∈ Finset.range (2 * (bilinear D left right).natAbs + 1),
            (clearedPolynomial (bilinear D left right)).coeff degree *
              halfIntegerBinomial
                (exponent - (chargeNorm D left - 2 * (bilinear D left right).natAbs) - degree)
                order) •
            tensorCommonKernel D hu left right exponent
              (total + chargeNorm D left + chargeNorm D right -
                2 * (bilinear D left right).natAbs - exponent) state := by
  classical
  let gram := bilinear D left right
  let firstShift := chargeNorm D left - 2 * (gram.natAbs : ℤ)
  let kernelTotal := total + chargeNorm D left + chargeNorm D right - 2 * (gram.natAbs : ℤ)
  let polynomial := clearedPolynomial gram
  let degrees := Finset.range (2 * gram.natAbs + 1)
  let term := fun (exponent : ℤ) (degree : ℕ) =>
    (polynomial.coeff degree * halfIntegerBinomial exponent order) •
      tensorCommonKernel D hu left right (exponent + firstShift + degree)
        (kernelTotal - (exponent + firstShift + degree)) state
  have finiteTerm (degree : ℕ) : Function.HasFiniteSupport (fun exponent => term exponent degree) := by
    simpa only [term, add_assoc] using
      LatticeHalfFockOriginalTwoSheetChartRecurrence.weighted_kernel_diagonal_finite D hu left right
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
    rw [(originalChartSupplier% cleared_ordered_kernel) D hu left right exponent (total - exponent)]
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
    simpa only [add_zero] using
      LatticeHalfFockOriginalTwoSheetChartRecurrence.weighted_kernel_diagonal_finite D hu left right
        kernelTotal 0 state (fun exponent => polynomial.coeff degree *
          halfIntegerBinomial (exponent - firstShift - degree) order)
  rw [sum_finsum_comm degrees _ (fun degree member => finiteReindexed degree)]
  apply congrArg ((chargeScalar D left * chargeScalar D right) • ·)
  apply finsum_congr
  intro exponent
  exact Finset.sum_smul.symm

theorem norm_add (D : LatticeData) (left right : Charge D) :
    chargeNorm D (left + right) =
      chargeNorm D left + chargeNorm D right + 2 * bilinear D left right := by
  have first : bilinear D (left + right) left = bilinear D left left + bilinear D right left := by
    simp [bilinear, add_mul, Finset.sum_add_distrib]
  have second : bilinear D (left + right) right =
      bilinear D left right + bilinear D right right := by
    simp [bilinear, add_mul, Finset.sum_add_distrib]
  unfold chargeNorm
  rw [LatticeActualGeneratorLocality.bilinear_add_right, first, second,
    LatticeFiniteNegativeGeneration.bilinear_symmetric D right left]
  ring

theorem scalar_normalization (D : LatticeData) (left right : Charge D) :
    (chargeScalar D left * chargeScalar D right) * (2 : ℂ) ^ (-2 * bilinear D left right) =
      chargeScalar D (left + right) := by
  unfold chargeScalar
  rw [← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0),
    ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0), norm_add]
  congr 1
  ring

private theorem local_plus_leading (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (total : ℤ) (state : ActualTensor D hu) :
    localPlus D hu left right
        (((bilinear D left right).natAbs + bilinear D left right : ℤ).toNat) total state =
      epsilon D left right • chargedCoefficient D hu (left + right)
        (total - 2 * (((bilinear D left right).natAbs + bilinear D left right : ℤ).toNat))
        state := by
  classical
  let gram := bilinear D left right
  let kernelTotal := total + chargeNorm D left + chargeNorm D right - 2 * (gram.natAbs : ℤ)
  have start : ((gram.natAbs + gram : ℤ).toNat) = 2 * gram.toNat := by omega
  change localPlus D hu left right ((gram.natAbs + gram : ℤ).toNat) total state = _
  rw [start, local_plus_kernel_expansion]
  dsimp only [gram]
  simp_rw [literal_clearing_leading_coefficient]
  have finite : Function.HasFiniteSupport (fun exponent : ℤ =>
      tensorCommonKernel D hu left right exponent (kernelTotal - exponent) state) := by
    simpa only [add_zero, one_smul] using
      LatticeHalfFockOriginalTwoSheetChartRecurrence.weighted_kernel_diagonal_finite D hu left right
        kernelTotal 0 state (fun _ => (1 : ℂ))
  change (chargeScalar D left * chargeScalar D right) •
    (∑ᶠ exponent : ℤ, (2 : ℂ) ^ (-2 * gram) •
      tensorCommonKernel D hu left right exponent (kernelTotal - exponent) state) = _
  rw [← smul_finsum' _ finite, tensor_common_kernel_diagonal_fusion,
    smul_smul, scalar_normalization]
  have index : kernelTotal - chargeNorm D (left + right) =
      total - 2 * (((gram.natAbs + gram : ℤ).toNat) : ℤ) := by
    dsimp [kernelTotal]
    rw [norm_add]
    omega
  rw [start] at index
  rw [index]
  simp only [chargedCoefficient, LinearMap.smul_apply]
  exact smul_comm (chargeScalar D (left + right)) (epsilon D left right) _

private theorem original_ground_mode (D : LatticeData) (left right : Charge D) :
    ((LatticeAllStateField.Y D (Finsupp.single left 1))[[-bilinear D left right - 1]])
        (Finsupp.single right 1) =
      epsilon D left right • Finsupp.single (left + right) 1 := by
  rw [LatticeAllStateField.stateField_ground, actualField, VertexOperator.ncoeff_of_coeff,
    (actual_creation_coefficient_transport D left right).2.2.1]
  have support : (1 : Polynomial (Oscillator D)).support = {0} := by
    simpa using Polynomial.support_C (show (1 : Oscillator D) ≠ 0 from one_ne_zero)
  simp [rawSingle, translatedPolynomial, support, creationCoeff,
    LatticeSugawaraConformal.exponential_constant]

theorem literal_plus_original_source (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (total : ℤ) (state : ActualTensor D hu) :
    localPlus D hu left right
        (((bilinear D left right).natAbs + bilinear D left right : ℤ).toNat) total state =
      (Ytw D hu (((LatticeAllStateField.Y D (Finsupp.single left 1))
          [[-bilinear D left right - 1]]) (Finsupp.single right 1))).coeff
        (total - 2 * (((bilinear D left right).natAbs + bilinear D left right : ℤ).toNat))
        state := by
  rw [local_plus_leading, original_ground_mode, map_smul, Ytw_charge]
  simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply,
    chargedField, HVertexOperator.coeff_of_coeff]

theorem literal_minus_original_source (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (total : ℤ) (state : ActualTensor D hu) :
    localMinus D hu left right
        (((bilinear D left right).natAbs - bilinear D left right : ℤ).toNat) total state =
      (Ytw D hu (((LatticeAllStateField.Y D (Finsupp.single (-left) 1))
          [[bilinear D left right - 1]]) (Finsupp.single right 1))).coeff
        (total - 2 * (((bilinear D left right).natAbs - bilinear D left right : ℤ).toNat))
        state := by
  change (∑ᶠ exponent : ℤ,
    (((-1 : ℂ) ^ exponent) * halfIntegerBinomial exponent
      (((bilinear D left right).natAbs - bilinear D left right : ℤ).toNat)) •
        clearedOrderedCoefficient D hu left right exponent (total - exponent) state) = _
  rw [LatticeHalfFockOriginalTwoSheetChartRecurrence.minus_sum_plus_neg]
  have opposite := literal_plus_original_source D hu (-left) right total state
  simpa only [LatticeFiniteNegativeGeneration.bilinear_neg_left, Int.natAbs_neg,
    ← sub_eq_add_neg, neg_neg] using opposite

end
end D5.S3.VertexAlgebra.LatticeHalfFockLiteralChargedLeading
