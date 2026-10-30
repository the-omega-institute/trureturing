/- GID: D5/S3/VertexAlgebra/LatticeHalfFockPhysicalLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockPhysicalLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual charged coefficients have physical two-branch locality on unrestricted tensor states. -/


import D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
import D5.S3.VertexAlgebra.LatticeHalfFockGroundProducts
import D5.S3.VertexAlgebra.LatticeHalfFockClearedKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/- Later reuse boundary: apply this unrestricted coefficient theorem to the
   two integer parity slices of the current chargedField: at modes m,n and
   integer slice shifts p,q, substitute first=-2*m-p-2, second=-2*n-q-2.
   FieldDeltaBinomial then reads the same doubled shifts as delta^N of the
   slice commutator. This is a later consumer, not a premise here. Combine that slice
   result with the existing current/current order-2, current/charged order-1
   and jet-locality source, without importing archived PhysicalRescaling or
   PhysicalGeneratorLocality (their old allstate/normal imports are excluded).
   Corrected descendant locality, normal561/corrected402, Jacobi and VOA
   reconstruction are separate, uncompiled obligations. -/
namespace D5.S3.VertexAlgebra.LatticeHalfFockPhysicalLocality

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockOrderedProducts
open LatticeHalfFockBranchClearing LatticeHalfFockClearedKernel
open FieldNormalProductLocality
open scoped BigOperators TensorProduct

noncomputable section

private def exchange {State : Type*} (value : ℤ → ℤ → State) : ℤ → ℤ → State :=
  fun first second => value second first

private theorem delta_exchange {State : Type*} [AddCommGroup State] [Module ℂ State]
    (value : ℤ → ℤ → Module.End ℂ State) (order : ℕ) :
    (deltaEnd ^ order) (exchange value) =
      ((-1 : ℂ) ^ order) • exchange ((deltaEnd ^ order) value) := by
  induction order with
  | zero => simp [exchange]
  | succ order inductionProof =>
    rw [pow_succ', Module.End.mul_apply, inductionProof]
    funext first second
    change ((-1 : ℂ) ^ order) • ((deltaEnd ^ order) value) second (first + 1) -
        ((-1 : ℂ) ^ order) • ((deltaEnd ^ order) value) (second + 1) first =
      ((-1 : ℂ) ^ (order + 1)) •
        (((deltaEnd ^ order) value) (second + 1) first -
          ((deltaEnd ^ order) value) second (first + 1))
    rw [pow_succ, mul_smul, neg_one_smul]
    module

def orderedProducts (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (firstExponent secondExponent : ℤ) :
    ℤ → ℤ → Module.End ℂ (ActualTensor D hu) :=
  fun first second => chargedCoefficient D hu left (firstExponent - 2 * first) *
    chargedCoefficient D hu right (secondExponent - 2 * second)

theorem product_pure (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) (polynomial : Oscillator D)
    (vector : ActualGround D hu) :
    chargedCoefficient D hu left first
        (chargedCoefficient D hu right second (polynomial ⊗ₜ[ℂ] vector)) =
      (chargeScalar D left * chargeScalar D right) •
        (coefficientExpansion D left right (halfContraction D left right) polynomial
          (first + chargeNorm D left) (second + chargeNorm D right) ⊗ₜ[ℂ]
            groundAction D hu left (groundAction D hu right vector)) := by
  have oscillator := native_ordered_product D left right
    (first + chargeNorm D left) (second + chargeNorm D right) polynomial
  simp only [add_sub_cancel_right] at oscillator
  change oscillatorCoefficient D left first (oscillatorCoefficient D right second polynomial) =
    coefficientExpansion D left right (halfContraction D left right) polynomial
      (first + chargeNorm D left) (second + chargeNorm D right) at oscillator
  simp only [chargedCoefficient, LinearMap.smul_apply, TensorProduct.map_tmul,
    map_smul, smul_smul, oscillator]
  module

theorem iterate_products_pure (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (firstExponent secondExponent : ℤ)
    (polynomial : Oscillator D) (vector : ActualGround D hu) (order : ℕ)
    (first second : ℤ) :
    ((deltaEnd ^ order) (orderedProducts D hu left right firstExponent secondExponent))
        first second (polynomial ⊗ₜ[ℂ] vector) =
      (chargeScalar D left * chargeScalar D right) •
        (((physicalDifference D ^ order)
            (coefficientExpansion D left right (halfContraction D left right) polynomial))
          (firstExponent + chargeNorm D left - 2 * first)
          (secondExponent + chargeNorm D right - 2 * second) ⊗ₜ[ℂ]
            groundAction D hu left (groundAction D hu right vector)) := by
  induction order generalizing first second with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, orderedProducts, Module.End.mul_apply]
    rw [product_pure]
    rw [show firstExponent - 2 * first + chargeNorm D left =
        firstExponent + chargeNorm D left - 2 * first by omega,
      show secondExponent - 2 * second + chargeNorm D right =
        secondExponent + chargeNorm D right - 2 * second by omega]
  | succ order inductionProof =>
    rw [pow_succ', Module.End.mul_apply]
    change (((deltaEnd ^ order)
        (orderedProducts D hu left right firstExponent secondExponent)) (first + 1) second -
      ((deltaEnd ^ order)
        (orderedProducts D hu left right firstExponent secondExponent)) first (second + 1))
      (polynomial ⊗ₜ[ℂ] vector) = _
    rw [LinearMap.sub_apply, inductionProof, inductionProof]
    rw [pow_succ', Module.End.mul_apply]
    have firstShift : firstExponent + chargeNorm D left - 2 * (first + 1) =
        firstExponent + chargeNorm D left - 2 * first - 2 := by omega
    have secondShift : secondExponent + chargeNorm D right - 2 * (second + 1) =
        secondExponent + chargeNorm D right - 2 * second - 2 := by omega
    rw [firstShift, secondShift]
    change _ = (chargeScalar D left * chargeScalar D right) •
      ((((physicalDifference D ^ order)
          (coefficientExpansion D left right (halfContraction D left right) polynomial))
          (firstExponent + chargeNorm D left - 2 * first - 2)
          (secondExponent + chargeNorm D right - 2 * second) -
        ((physicalDifference D ^ order)
          (coefficientExpansion D left right (halfContraction D left right) polynomial))
          (firstExponent + chargeNorm D left - 2 * first)
          (secondExponent + chargeNorm D right - 2 * second - 2)) ⊗ₜ[ℂ]
            groundAction D hu left (groundAction D hu right vector))
    rw [TensorProduct.sub_tmul, smul_sub]

private theorem commutator_iterate_pure (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) (polynomial : Oscillator D)
    (vector : ActualGround D hu) :
    ((deltaEnd ^ (bilinear D left right).natAbs)
      (orderedProducts D hu left right first second -
        exchange (orderedProducts D hu right left second first)))
      0 0 (polynomial ⊗ₜ[ℂ] vector) = 0 := by
  rw [map_sub]
  change ((deltaEnd ^ (bilinear D left right).natAbs)
      (orderedProducts D hu left right first second)) 0 0 (polynomial ⊗ₜ[ℂ] vector) -
    ((deltaEnd ^ (bilinear D left right).natAbs)
      (exchange (orderedProducts D hu right left second first))) 0 0
        (polynomial ⊗ₜ[ℂ] vector) = 0
  rw [delta_exchange]
  simp only [Pi.smul_apply, exchange, LinearMap.smul_apply]
  rw [iterate_products_pure, iterate_products_pure]
  simp only [mul_zero, sub_zero]
  have kernel := native_cleared_kernel_exchange D left right polynomial
    (first + chargeNorm D left) (second + chargeNorm D right)
  have ground : groundAction D hu left (groundAction D hu right vector) =
      ((-1 : ℂ) ^ (bilinear D left right).natAbs) •
        groundAction D hu right (groundAction D hu left vector) := by
    have native := LatticeHalfFockGroundProducts.ground_action_exchange D hu left right
    change groundAction D hu left * groundAction D hu right =
      paritySign (bilinear D left right) •
        (groundAction D hu right * groundAction D hu left) at native
    simpa only [Module.End.mul_apply, LinearMap.smul_apply,
      ← physical_clearing_sign (bilinear D left right)] using
      congrArg (fun operator : Module.End ℂ (ActualGround D hu) => operator vector) native
  rw [kernel, ground]
  simp only [TensorProduct.tmul_smul]
  module

theorem charged_coefficient_physical_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) (state : ActualTensor D hu) :
    ∑ offset ∈ Finset.range ((bilinear D left right).natAbs + 1),
      (((-1 : ℂ) ^ offset) * ((bilinear D left right).natAbs.choose offset : ℂ)) •
        (chargedCoefficient D hu left
            (first - 2 * (((bilinear D left right).natAbs - offset : ℕ) : ℤ))
            (chargedCoefficient D hu right (second - 2 * (offset : ℤ)) state) -
          chargedCoefficient D hu right (second - 2 * (offset : ℤ))
            (chargedCoefficient D hu left
              (first - 2 * (((bilinear D left right).natAbs - offset : ℕ) : ℤ)) state)) = 0 := by
  classical
  let order := (bilinear D left right).natAbs
  let readout : Module.End ℂ (ActualTensor D hu) :=
    ∑ offset ∈ Finset.range (order + 1),
      (((-1 : ℂ) ^ offset) * (order.choose offset : ℂ)) •
        (chargedCoefficient D hu left (first - 2 * ((order - offset : ℕ) : ℤ)) *
            chargedCoefficient D hu right (second - 2 * (offset : ℤ)) -
          chargedCoefficient D hu right (second - 2 * (offset : ℤ)) *
            chargedCoefficient D hu left (first - 2 * ((order - offset : ℕ) : ℤ)))
  have identification : readout =
      ((deltaEnd ^ order) (orderedProducts D hu left right first second -
        exchange (orderedProducts D hu right left second first))) 0 0 := by
    rw [FieldDeltaBinomial.delta_binomial]
    apply Finset.sum_congr rfl
    intro offset supported
    have bound : offset ≤ order := by
      have present := Finset.mem_range.mp supported
      omega
    simp only [orderedProducts, exchange, Pi.sub_apply, zero_add]
    rw [Int.natCast_sub bound]
  suffices readout state = 0 by
    simpa only [readout, order, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.sub_apply, Module.End.mul_apply] using this
  induction state using TensorProduct.induction_on with
  | zero => exact map_zero readout
  | add firstState secondState firstProof secondProof =>
    rw [map_add, firstProof, secondProof, add_zero]
  | tmul polynomial vector =>
    rw [identification]
    exact commutator_iterate_pure D hu left right first second polynomial vector

end
end D5.S3.VertexAlgebra.LatticeHalfFockPhysicalLocality
