/- GID: D5/S3/VertexAlgebra/LatticeHalfFockChargedTranslationExtension
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockChargedTranslationExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual charged physical differentiation on the full algebraic tensor carrier. -/

import D5.S3.VertexAlgebra.LatticeHalfFockChargedTranslation

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedTranslationExtension

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open LatticeHalfFockFirstDescendant LatticeHalfFockTranslationCalculus
open LatticeHalfFockFirstDescendantCuts LatticeHalfFockAllStateField
open LatticeHalfFock LatticeHalfFockChargedTranslation MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

private theorem charged_creation_relation (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (index : Index D) (exponent : ℤ) (vector : ActualTensor D hu) :
    chargedCoefficient D hu charge exponent
        (tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1) vector) =
      tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1)
        (chargedCoefficient D hu charge exponent vector) -
      (bilinear D (unitCharge D index.1) charge : ℂ) •
        chargedCoefficient D hu charge (exponent + 2 * index.2 + 1) vector := by
  have ward := congrArg (fun operator : Module.End ℂ (ActualTensor D hu) => operator vector)
    (charged_tensor_current_ward D hu index.1 charge (-(index.2 : ℤ) - 1) exponent)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at ward
  rw [show exponent - (2 * (-(index.2 : ℤ) - 1) + 1) =
      exponent + 2 * index.2 + 1 by omega] at ward
  exact eq_sub_of_add_eq' (sub_eq_iff_eq_add.mp ward).symm

private theorem tensor_creation_commutator (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin D.rank) (index : Index D) (mode : ℤ) (vector : ActualTensor D hu) :
    tensorCurrent D (ActualGround D hu) colour mode
        (tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1) vector) -
      tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1)
        (tensorCurrent D (ActualGround D hu) colour mode vector) =
      (if mode = (index.2 : ℤ) then frequency mode * (D.G colour index.1 : ℂ) else 0) •
        vector := by
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul polynomial ground =>
    simp only [tensorCurrent, tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply]
    rw [← TensorProduct.sub_tmul, current_heisenberg_apply]
    by_cases same : mode = (index.2 : ℤ)
    · rw [if_pos (by omega : mode + (-(index.2 : ℤ) - 1) + 1 = 0), if_pos same,
        ← TensorProduct.smul_tmul']
    · rw [if_neg (by omega : mode + (-(index.2 : ℤ) - 1) + 1 ≠ 0), if_neg same]
      simp
  | add first second firstProof secondProof =>
    simp only [map_add, add_sub_add_comm, firstProof, secondProof, smul_add]

private theorem combination_creation_relation (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (index : Index D) (mode : ℤ) (vector : ActualTensor D hu) :
    currentCombination D hu (fun colour => (charge colour : ℂ)) mode
        (tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1) vector) =
      tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1)
        (currentCombination D hu (fun colour => (charge colour : ℂ)) mode vector) +
      (if mode = (index.2 : ℤ) then
        frequency mode * (bilinear D (unitCharge D index.1) charge : ℂ) else 0) • vector := by
  apply sub_eq_iff_eq_add'.mp
  simp only [currentCombination, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    map_smul, ← smul_sub, ← Finset.sum_sub_distrib, tensor_creation_commutator,
    smul_smul, ← Finset.sum_smul]
  congr 1
  by_cases same : mode = (index.2 : ℤ)
  · simp only [if_pos same]
    rw [LatticeFiniteNegativeGeneration.bilinear_symmetric D (unitCharge D index.1)]
    simp only [bilinear, unitCharge, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Int.cast_sum, Int.cast_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro colour member
    simp only [Finset.mem_univ, if_true, Int.cast_mul]
    ring
  · simp [same]

private theorem cutSummand_creation_relation (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (index : Index D) (exponent mode : ℤ) (vector : ActualTensor D hu) :
    cutSummand D hu (fun colour => (charge colour : ℂ)) charge exponent 0 mode
        (tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1) vector) =
      tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1)
        (cutSummand D hu (fun colour => (charge colour : ℂ)) charge exponent 0 mode vector) -
      (bilinear D (unitCharge D index.1) charge : ℂ) •
        cutSummand D hu (fun colour => (charge colour : ℂ)) charge
          (exponent + 2 * index.2 + 1) 0 mode vector +
      if mode = (index.2 : ℤ) then
        (frequency mode * (bilinear D (unitCharge D index.1) charge : ℂ)) •
          chargedCoefficient D hu charge (exponent + 2 * index.2 + 3) vector else 0 := by
  by_cases negative : mode < 0
  · have distinct : mode ≠ (index.2 : ℤ) := by omega
    simp only [cutSummand, if_pos negative, if_neg distinct, add_zero, Module.End.mul_apply]
    rw [charged_creation_relation, map_sub, map_smul, combination_creation_relation]
    simp only [if_neg distinct, zero_smul, add_zero]
    rw [show exponent + 2 * mode + 3 + 2 * index.2 + 1 =
        exponent + 2 * index.2 + 1 + 2 * mode + 3 by omega]
  · simp only [cutSummand, if_neg negative, Module.End.mul_apply]
    rw [combination_creation_relation, map_add, map_smul, charged_creation_relation]
    rw [show exponent + 2 * mode + 3 + 2 * index.2 + 1 =
        exponent + 2 * index.2 + 1 + 2 * mode + 3 by omega]
    by_cases same : mode = (index.2 : ℤ)
    · rw [if_pos same, if_pos same, same]
    · simp only [if_neg same, zero_smul, add_zero]

private theorem cutProduct_creation_relation (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (index : Index D) (exponent : ℤ) (vector : ActualTensor D hu) :
    cutProduct D hu (fun colour => (charge colour : ℂ)) charge exponent 0
        (tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1) vector) =
      tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1)
        (cutProduct D hu (fun colour => (charge colour : ℂ)) charge exponent 0 vector) -
      (bilinear D (unitCharge D index.1) charge : ℂ) •
        cutProduct D hu (fun colour => (charge colour : ℂ)) charge
          (exponent + 2 * index.2 + 1) 0 vector +
      (frequency index.2 * (bilinear D (unitCharge D index.1) charge : ℂ)) •
        chargedCoefficient D hu charge (exponent + 2 * index.2 + 3) vector := by
  let creator := tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1)
  let base := fun mode => cutSummand D hu (fun colour => (charge colour : ℂ))
    charge exponent 0 mode vector
  let shifted := fun mode => cutSummand D hu (fun colour => (charge colour : ℂ))
    charge (exponent + 2 * index.2 + 1) 0 mode vector
  let deltaTerm := fun mode : ℤ => if mode = (index.2 : ℤ) then
    (frequency mode * (bilinear D (unitCharge D index.1) charge : ℂ)) •
      chargedCoefficient D hu charge (exponent + 2 * index.2 + 3) vector else 0
  have baseFinite := cutSummand_finite D hu (fun colour => (charge colour : ℂ))
    charge exponent 0 vector
  have shiftedFinite := cutSummand_finite D hu (fun colour => (charge colour : ℂ))
    charge (exponent + 2 * index.2 + 1) 0 vector
  change Function.HasFiniteSupport base at baseFinite
  change Function.HasFiniteSupport shifted at shiftedFinite
  have deltaFinite : Function.HasFiniteSupport deltaTerm := by
    apply (Set.finite_singleton (index.2 : ℤ)).subset
    intro mode member
    by_contra distinct
    have different : mode ≠ (index.2 : ℤ) := by simpa using distinct
    exact member (by simp [deltaTerm, different])
  change (∑ᶠ mode : ℤ, cutSummand D hu (fun colour => (charge colour : ℂ))
      charge exponent 0 mode (creator vector)) =
    creator (∑ᶠ mode : ℤ, base mode) -
      (bilinear D (unitCharge D index.1) charge : ℂ) • (∑ᶠ mode : ℤ, shifted mode) + _
  have mapped := creator.toAddMonoidHom.map_finsum baseFinite
  change creator (∑ᶠ mode : ℤ, base mode) = ∑ᶠ mode : ℤ, creator (base mode) at mapped
  rw [mapped, smul_finsum' _ shiftedFinite]
  rw [← finsum_sub_distrib (baseFinite.fun_comp creator.map_zero)
    (shiftedFinite.fun_comp (smul_zero (bilinear D (unitCharge D index.1) charge : ℂ)))]
  have single : (∑ᶠ mode : ℤ, deltaTerm mode) =
      (frequency index.2 * (bilinear D (unitCharge D index.1) charge : ℂ)) •
        chargedCoefficient D hu charge (exponent + 2 * index.2 + 3) vector := by
    rw [finsum_eq_single _ (index.2 : ℤ)]
    · simp [deltaTerm]
    · intro mode distinct
      simp [deltaTerm, distinct]
  have differenceFinite : Function.HasFiniteSupport (fun mode => creator (base mode) -
      (bilinear D (unitCharge D index.1) charge : ℂ) • shifted mode) :=
    (baseFinite.fun_comp creator.map_zero).sub
      (shiftedFinite.fun_comp (smul_zero (bilinear D (unitCharge D index.1) charge : ℂ)))
  rw [← single, ← finsum_add_distrib differenceFinite deltaFinite]
  apply finsum_congr
  intro mode
  exact cutSummand_creation_relation D hu charge index exponent mode vector

private theorem source_ground_translation (D : LatticeData) (charge : Charge D) :
    LatticeSugawaraConformal.translation D (Finsupp.single charge 1) =
      originalFirstDescendant D (fun colour => (charge colour : ℂ)) charge := by
  simp [LatticeSugawaraConformal.translation_single, LatticeSugawaraConformal.chargePolynomial,
    originalFirstDescendant, Finsupp.single_finsetSum, Finsupp.smul_single]

private theorem charge_pairing_self (D : LatticeData) (charge : Charge D) :
    chargePairing D (fun colour => (charge colour : ℂ)) charge =
      (chargeNorm D charge : ℂ) := by
  simp [chargePairing, chargeNorm, bilinear, unitCharge, Int.cast_sum,
    Finset.mul_sum, mul_assoc]

private theorem cutProduct_ground (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : ℤ) (ground : ActualGround D hu) :
    cutProduct D hu (fun colour => (charge colour : ℂ)) charge exponent 0
        ((1 : Oscillator D) ⊗ₜ[ℂ] ground) =
      (((exponent + chargeNorm D charge + 2 : ℤ) : ℂ) / 2) •
        chargedCoefficient D hu charge (exponent + 2) ((1 : Oscillator D) ⊗ₜ[ℂ] ground) := by
  have differentiated := original_ground_translation_physical D hu charge exponent ground
  rw [source_ground_translation, Ytw_charge] at differentiated
  have corrected := native_first_descendant_coefficient D hu
    (fun colour => (charge colour : ℂ)) charge exponent ((1 : Oscillator D) ⊗ₜ[ℂ] ground)
  rw [charge_pairing_self] at corrected
  change _ = (((exponent + 2 : ℤ) : ℂ) / 2) •
    chargedCoefficient D hu charge (exponent + 2) ((1 : Oscillator D) ⊗ₜ[ℂ] ground)
      at differentiated
  rw [corrected] at differentiated
  rw [sub_eq_iff_eq_add] at differentiated
  rw [differentiated, ← add_smul]
  congr 1
  push_cast
  ring

private theorem cutProduct_polynomial (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Oscillator D) (ground : ActualGround D hu) :
    ∀ exponent : ℤ,
      cutProduct D hu (fun colour => (charge colour : ℂ)) charge exponent 0
          (polynomial ⊗ₜ[ℂ] ground) =
        (((exponent + chargeNorm D charge + 2 : ℤ) : ℂ) / 2) •
          chargedCoefficient D hu charge (exponent + 2) (polynomial ⊗ₜ[ℂ] ground) := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar =>
    intro exponent
    have constant : (C scalar : Oscillator D) ⊗ₜ[ℂ] ground =
        scalar • ((1 : Oscillator D) ⊗ₜ[ℂ] ground) := by
      rw [TensorProduct.smul_tmul', MvPolynomial.smul_eq_C_mul, mul_one]
    rw [constant, map_smul, map_smul, cutProduct_ground, smul_comm]
  | add first second firstProof secondProof =>
    intro exponent
    simp only [TensorProduct.add_tmul, map_add, firstProof, secondProof, smul_add]
  | mul_X polynomial index previous =>
    intro exponent
    have created : (polynomial * X index) ⊗ₜ[ℂ] ground =
        tensorCurrent D (ActualGround D hu) index.1 (-(index.2 : ℤ) - 1)
          (polynomial ⊗ₜ[ℂ] ground) := by
      simp only [tensorCurrent, tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply,
        current_negative, LinearMap.mulLeft_apply]
      rw [mul_comm]
    rw [created, cutProduct_creation_relation, previous exponent,
      previous (exponent + 2 * index.2 + 1), charged_creation_relation, map_smul]
    rw [show exponent + 2 + 2 * index.2 + 1 = exponent + 2 * index.2 + 3 by omega]
    rw [show exponent + 2 * index.2 + 1 + 2 = exponent + 2 * index.2 + 3 by omega]
    simp only [frequency, smul_sub, smul_smul]
    push_cast
    module

private theorem cutProduct_all_tensor (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : ℤ) (vector : ActualTensor D hu) :
    cutProduct D hu (fun colour => (charge colour : ℂ)) charge exponent 0 vector =
      (((exponent + chargeNorm D charge + 2 : ℤ) : ℂ) / 2) •
        chargedCoefficient D hu charge (exponent + 2) vector := by
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul polynomial ground => exact cutProduct_polynomial D hu charge polynomial ground exponent
  | add first second firstProof secondProof =>
    simp only [map_add, firstProof, secondProof, smul_add]

theorem charged_physical_translation (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) :
    Ytw D hu (LatticeSugawaraConformal.translation D (Finsupp.single charge 1)) =
      physicalDerivative D hu (chargedField D hu charge) := by
  rw [source_ground_translation]
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  rw [native_first_descendant_coefficient, charge_pairing_self, cutProduct_all_tensor]
  change (((exponent + chargeNorm D charge + 2 : ℤ) : ℂ) / 2) •
      chargedCoefficient D hu charge (exponent + 2) vector -
    ((chargeNorm D charge : ℂ) / 2) • chargedCoefficient D hu charge (exponent + 2) vector =
      (((exponent + 2 : ℤ) : ℂ) / 2) • chargedCoefficient D hu charge (exponent + 2) vector
  rw [← sub_smul]
  congr 1
  push_cast
  ring

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedTranslationExtension

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockChargedTranslationExtension.charged_physical_translation
