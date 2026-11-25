/- GID: D5/S3/VertexAlgebra/TwistedGround/Charge/NativeChargeGeometry
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Charge/NativeChargeGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The literal chosen native ground inherits positive geometry and signed adjoints. -/

import D5.S3.VertexAlgebra.TwistedGround.Charge.ChargeHermitian
import D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.NativeChargeGeometry

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient TwistedGround.OperatorAlgebra
open TwistedGround.ChargeGeometry TwistedGround.ChargeHermitian
open LatticeHalfFockChargedTensorCoefficients
open scoped BigOperators

noncomputable section

private theorem original_inverse_action (D : LatticeData) {rank : ℕ}
    (rho : Representation ℂ (Extension D ⧸ K D) (Ground rank))
    (central : rho (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
      -(1 : Module.End ℂ (Ground rank))) (charge : Charge D) :
    rho (QuotientGroup.mk (⟨0, charge⟩ : Extension D))⁻¹ =
      complexSign (integralCocycle D charge charge) •
        rho (QuotientGroup.mk (⟨0, -charge⟩ : Extension D)) := by
  let signElement : Extension D ⧸ K D :=
    QuotientGroup.mk (⟨integralCocycle D charge charge, 0⟩ : Extension D)
  have sign_reduction : quotientEquiv D signElement =
      ⟨integralCocycle D charge charge, 0⟩ := by
    change reduction D (⟨integralCocycle D charge charge, 0⟩ : Extension D) = _
    ext index
    · rfl
    · simp [reduction, reduceCharge]
  have sign_action := charge_right_translation D rho central 0 signElement
  simp only [charge_zero, one_mul] at sign_action
  have sign_charge : quotientCharge D signElement = 0 := by
    simp [quotientCharge, sign_reduction]
  simp only [translationSign, sign_reduction, sign_charge, map_zero,
    add_zero, charge_zero] at sign_action
  have group_inverse : (QuotientGroup.mk (⟨0, charge⟩ : Extension D))⁻¹ =
      signElement * QuotientGroup.mk (⟨0, -charge⟩ : Extension D) := by
    change (QuotientGroup.mk' (K D) (⟨0, charge⟩ : Extension D))⁻¹ =
      QuotientGroup.mk' (K D) (⟨integralCocycle D charge charge, 0⟩ : Extension D) *
        QuotientGroup.mk' (K D) (⟨0, -charge⟩ : Extension D)
    rw [← map_inv, ← map_mul]
    congr 1
    ext index
    · change -0 + integralCocycle D charge charge =
        integralCocycle D charge charge + 0 + integralCocycle D 0 (-charge)
      simp
    · change -charge index = (0 : Charge D) index + (-charge) index
      simp
  rw [group_inverse, map_mul, sign_action, smul_mul_assoc, one_mul]

theorem native_ground_signed_adjoint (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (first second : ActualGround D hu) :
    chargeForm D (groundRepresentation D hu) (groundAction D hu charge first) second =
      epsilon D charge charge *
        chargeForm D (groundRepresentation D hu) first (groundAction D hu (-charge) second) ∧
    epsilon D charge charge = paritySign (bilinear D charge charge / 2) := by
  have properties := Classical.choose_spec
    (Classical.choose_spec (actual_twisted_ground_representation D hu))
  have central : groundRepresentation D hu (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
      -(1 : Module.End ℂ (ActualGround D hu)) := properties.2.2.1
  constructor
  · rw [groundAction, groundLift,
      charge_form_inverse_adjoint D (groundRepresentation D hu) central,
      original_inverse_action D (groundRepresentation D hu) central]
    simp only [LinearMap.smul_apply, charge_form_smul_right]
    rw [show complexSign (integralCocycle D charge charge) = epsilon D charge charge from
      complexSign_integral (lowerCocycleExponent D charge charge)]
    rfl
  · exact congrArg paritySign (integral_cocycle_square D charge)

#print axioms native_ground_signed_adjoint

end

end D5.S3.VertexAlgebra.TwistedGround.NativeChargeGeometry
