/- GID: D5/S3/VertexAlgebra/TwistedGround/Charge/ChargeGeometry
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Charge/ChargeGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original canonical charges act by signed translations and Gram characters. -/

import D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.ChargeGeometry

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient TwistedGround.OperatorAlgebra
open scoped BigOperators

noncomputable section

variable (D : LatticeData) {rank : ℕ}
variable (rho : Representation ℂ (Extension D ⧸ K D) (Ground rank))
variable (central : rho (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
  -(1 : Module.End ℂ (Ground rank)))

private theorem reduced_charge_lift (charge : ModTwoCharge D) :
    quotientEquiv D (chargeLift D charge) = ⟨0, charge⟩ := by
  change reduction D (⟨0, integralLift D charge⟩ : Extension D) = _
  ext index
  · rfl
  · simp [reduction, reduceCharge, integralLift]

include central in
private theorem sign_action (sign : F₂) :
    rho ((quotientEquiv D).symm (⟨sign, 0⟩ : ReducedExtension D)) =
      complexSign sign • (1 : Module.End ℂ (Ground rank)) := by
  fin_cases sign
  · have identity : (⟨0, 0⟩ : ReducedExtension D) = 1 := rfl
    simp [identity, sign_zero]
  · have negative : (quotientEquiv D).symm (⟨1, 0⟩ : ReducedExtension D) =
        QuotientGroup.mk (⟨1, 0⟩ : Extension D) := by
      apply (quotientEquiv D).injective
      rw [MulEquiv.apply_symm_apply]
      change (⟨1, 0⟩ : ReducedExtension D) = reduction D (⟨1, 0⟩ : Extension D)
      ext index
      · rfl
      · simp [reduction, reduceCharge]
    change rho ((quotientEquiv D).symm (⟨1, 0⟩ : ReducedExtension D)) = complexSign 1 • 1
    rw [negative, central, sign_one]
    exact (neg_one_smul ℂ (1 : Module.End ℂ (Ground rank))).symm

theorem charge_zero : chargeOperator D rho 0 = 1 := by
  have identity : chargeLift D 0 = 1 := by
    apply (quotientEquiv D).injective
    rw [reduced_charge_lift, map_one]
    rfl
  simp [chargeOperator, identity]

def translationSign (charge : ModTwoCharge D) (element : Extension D ⧸ K D) : F₂ :=
  (quotientEquiv D element).sign + modTwoCocycle D charge (quotientCharge D element)

include central in
theorem charge_right_translation (charge : ModTwoCharge D)
    (element : Extension D ⧸ K D) :
    chargeOperator D rho charge * rho element =
      complexSign (translationSign D charge element) •
        chargeOperator D rho (charge + quotientCharge D element) := by
  have product : chargeLift D charge * element =
      (quotientEquiv D).symm (⟨translationSign D charge element, 0⟩ : ReducedExtension D) *
        chargeLift D (charge + quotientCharge D element) := by
    apply (quotientEquiv D).injective
    simp only [map_mul, MulEquiv.apply_symm_apply, reduced_charge_lift]
    apply SignExtension.ext
    · change 0 + (quotientEquiv D element).sign +
          modTwoCocycle D charge (quotientEquiv D element).charge =
        translationSign D charge element + 0 + modTwoCocycle D 0 _
      simp [translationSign, quotientCharge]
    · change charge + (quotientEquiv D element).charge = 0 + _
      simp [quotientCharge]
  unfold chargeOperator
  rw [← map_mul, product, map_mul, sign_action D rho central, smul_mul_assoc, one_mul]

theorem translation_sign_unit (charge : ModTwoCharge D) (element : Extension D ⧸ K D) :
    starRingEnd ℂ (complexSign (translationSign D charge element)) *
      complexSign (translationSign D charge element) = 1 := by
  simp only [complexSign]
  split_ifs <;> norm_num

include central in
theorem charge_conjugation (first second : ModTwoCharge D) :
    chargeOperator D rho first * chargeOperator D rho second * dualOperator D rho first =
      complexSign (modTwoPairing D first second) • chargeOperator D rho second := by
  have commutation : chargeLift D first * chargeLift D second =
      (quotientEquiv D).symm (⟨modTwoPairing D first second, 0⟩ : ReducedExtension D) *
        (chargeLift D second * chargeLift D first) := by
    apply (quotientEquiv D).injective
    simp only [map_mul, MulEquiv.apply_symm_apply, reduced_charge_lift]
    exact reduced_commutation D _ _
  unfold chargeOperator dualOperator
  rw [← map_mul, commutation, map_mul, sign_action D rho central, map_mul,
    smul_mul_assoc, one_mul, smul_mul_assoc, mul_assoc, ← map_mul,
    mul_inv_cancel, map_one, mul_one]

def gramCharacter (charge : ModTwoCharge D) : AddChar (ModTwoCharge D) ℂ where
  toFun partner := complexSign (modTwoPairing D partner charge)
  map_zero_eq_one' := by simp [sign_zero]
  map_add_eq_mul' first second := by
    rw [map_add, LinearMap.add_apply, complexSign_add]

theorem gram_character_sum (hu : IsUnit D.G.det) (charge : ModTwoCharge D) :
    ∑ partner : ModTwoCharge D, complexSign (modTwoPairing D partner charge) =
      if charge = 0 then (Fintype.card (ModTwoCharge D) : ℂ) else 0 := by
  classical
  by_cases vanished : charge = 0
  · simp [vanished, sign_zero]
  · rw [if_neg vanished]
    change ∑ partner, gramCharacter D charge partner = 0
    have exists_partner : ∃ partner, modTwoPairing D partner charge ≠ 0 := by
      by_contra absent
      push Not at absent
      exact vanished ((mod_two_pairing_nondegenerate D hu).2 charge absent)
    obtain ⟨partner, nonzero_pairing⟩ := exists_partner
    apply AddChar.sum_eq_zero_of_ne_one
    intro trivial
    have value := congrArg (fun character : AddChar (ModTwoCharge D) ℂ =>
      character partner) trivial
    change complexSign (modTwoPairing D partner charge) = 1 at value
    generalize equation : modTwoPairing D partner charge = bit at *
    fin_cases bit <;> norm_num [sign_one] at *

end

end D5.S3.VertexAlgebra.TwistedGround.ChargeGeometry
