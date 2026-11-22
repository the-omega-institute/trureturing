/- GID: D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockChargedHermitian
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockChargedHermitian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native chosen-tensor charged coefficients and original field have signed adjoints. -/

import D5.S3.VertexAlgebra.HalfFock.Hermitian.LatticeHalfFockConvolutionAdjoint
import D5.S3.VertexAlgebra.HalfFock.Hermitian.LatticeHalfFockTensorHermitian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedHermitian

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeHalfFockHermitian LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockConvolutionAdjoint
open LatticeHalfFockTensorHermitian TwistedGround.ChargeHermitian
open scoped TensorProduct

noncomputable section

private theorem charge_scalar_real (D : LatticeData) (charge : Charge D) :
    starRingEnd ℂ (chargeScalar D charge) = chargeScalar D charge := by
  have real_two : starRingEnd ℂ (2 : ℂ) = 2 := Complex.conj_ofReal (2 : ℝ)
  rw [chargeScalar, map_zpow₀, real_two]

private theorem charge_scalar_reflection (D : LatticeData) (charge : Charge D) :
    chargeScalar D (-charge) = chargeScalar D charge := by
  simp [chargeScalar, chargeNorm, bilinear_neg_left, bilinear_neg_right]

private theorem charged_coefficient_adjoint (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : ℤ) (left right : ActualTensor D hu) :
    tensorForm D hu (chargedCoefficient D hu charge exponent left) right =
      epsilon D charge charge * tensorForm D hu left
        (chargedCoefficient D hu (-charge) (-exponent - 2 * chargeNorm D charge) right) := by
  induction left using TensorProduct.induction_on with
  | zero => simp
  | add first second firstProof secondProof =>
      simp only [map_add, LinearMap.add_apply, firstProof, secondProof, mul_add]
  | tmul polynomial ground =>
      induction right using TensorProduct.induction_on with
      | zero => simp
      | add first second firstProof secondProof =>
          simp only [map_add, firstProof, secondProof, mul_add]
      | tmul other target =>
          simp only [chargedCoefficient, LinearMap.smul_apply, TensorProduct.map_tmul,
            LinearMap.map_smulₛₗ, map_smul, charge_scalar_real, charge_scalar_reflection,
            tensorForm_tmul, smul_eq_mul]
          rw [oscillator_coefficient_adjoint,
            (TwistedGround.NativeChargeGeometry.native_ground_signed_adjoint
              D hu charge ground target).1]
          ring

theorem charged_coefficient_field_adjoint (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : ℤ) (left right : ActualTensor D hu) :
    tensorForm D hu (chargedCoefficient D hu charge exponent left) right =
      epsilon D charge charge * tensorForm D hu left
        (chargedCoefficient D hu (-charge) (-exponent - 2 * chargeNorm D charge) right) ∧
    tensorForm D hu ((chargedField D hu charge).coeff exponent left) right =
      epsilon D charge charge * tensorForm D hu left
        ((chargedField D hu (-charge)).coeff (-exponent - 2 * chargeNorm D charge) right) := by
  have native := charged_coefficient_adjoint D hu charge exponent left right
  exact ⟨native, by simpa only [chargedField, HVertexOperator.coeff_of_coeff] using native⟩

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedHermitian
