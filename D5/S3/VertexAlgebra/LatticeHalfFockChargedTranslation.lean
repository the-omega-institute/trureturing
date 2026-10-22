/- GID: D5/S3/VertexAlgebra/LatticeHalfFockChargedTranslation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockChargedTranslation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual charged exponential differentiation with the physical doubled shift. -/

import D5.S3.VertexAlgebra.LatticeHalfFockTranslationCalculus
import D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendantCuts

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedTranslation

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open LatticeHalfFockFirstDescendant LatticeHalfFockTranslationCalculus
open LatticeHalfFockFirstDescendantCuts LatticeHalfFockAllStateField
open LatticeHalfFock
open MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

def creationDerivativeTerm (D : LatticeData) (charge : Charge D) (degree : ℤ)
    (offset : ℕ) : Oscillator D :=
  (∑ colour : Fin D.rank, (charge colour : ℂ) • X (colour, offset)) *
    halfCreationCoeff D charge (degree - 1 - 2 * offset)

private theorem creationDerivativeTerm_finite (D : LatticeData) (charge : Charge D)
    (degree : ℤ) : Function.HasFiniteSupport (creationDerivativeTerm D charge degree) := by
  apply (Finset.range (degree.toNat + 1)).finite_toSet.subset
  intro offset member
  by_contra outside
  have bound : degree - 1 - 2 * (offset : ℤ) < 0 := by
    simp only [Finset.mem_coe, Finset.mem_range, not_lt] at outside
    omega
  exact member (by simp [creationDerivativeTerm, halfCreationCoeff, bound])

private theorem creation_derivative_natural (D : LatticeData) (charge : Charge D)
    (degree : ℕ) :
    (degree + 1 : ℂ) • PowerSeries.coeff (degree + 1) (halfCreationExponential D charge) =
      (2 : ℂ) • ∑ offset ∈ Finset.range (degree / 2 + 1),
        creationDerivativeTerm D charge (degree + 1) offset := by
  have differentiated := congrArg (PowerSeries.coeff degree) (exponential_derivative D charge)
  rw [PowerSeries.coeff_derivative, mul_comm (halfCreationExponential D charge),
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at differentiated
  have scalar : (degree + 1 : Oscillator D) =
      algebraMap ℂ (Oscillator D) (degree + 1 : ℂ) := by simp
  rw [scalar, mul_comm _ (algebraMap ℂ (Oscillator D) (degree + 1 : ℂ)),
    ← Algebra.smul_def] at differentiated
  rw [differentiated]
  simp only [series_derivative_coeff, Prod.fst, Prod.snd, ite_mul, zero_mul,
    smul_mul_assoc]
  rw [← Finset.sum_filter]
  rw [← Finset.smul_sum]
  apply congrArg (fun polynomial : Oscillator D => (2 : ℂ) • polynomial)
  symm
  apply Finset.sum_bij (fun offset _ => 2 * offset)
  · intro offset member
    simp only [Finset.mem_filter, Finset.mem_range] at member ⊢
    omega
  · intro first firstMember second secondMember equality
    omega
  · intro index member
    simp only [Finset.mem_filter, Finset.mem_range] at member
    refine ⟨index / 2, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro offset member
    have bound : 2 * offset ≤ degree := by
      simp only [Finset.mem_range] at member
      omega
    have equality : (degree : ℤ) + 1 - 1 - 2 * offset =
        ((degree - 2 * offset : ℕ) : ℤ) := by
      omega
    simp only [creationDerivativeTerm, Nat.cast_add, Nat.cast_one, equality, halfCreationCoeff,
      if_neg (by omega : ¬ ((degree - 2 * offset : ℕ) : ℤ) < 0),
      Int.toNat_natCast, Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      smul_mul_assoc]

private theorem creation_physical_recurrence (D : LatticeData) (charge : Charge D)
    (degree : ℤ) :
    ((degree : ℂ) / 2) • halfCreationCoeff D charge degree =
      ∑ᶠ offset : ℕ, creationDerivativeTerm D charge degree offset := by
  by_cases positive : 0 < degree
  · have natural : degree = ((degree - 1).toNat + 1 : ℕ) := by omega
    have differentiated := creation_derivative_natural D charge (degree - 1).toNat
    rw [show ((degree - 1).toNat : ℤ) + 1 = degree by omega] at differentiated
    have contained : Function.support (creationDerivativeTerm D charge degree) ⊆
        Finset.range ((degree - 1).toNat / 2 + 1) := by
      intro offset member
      by_contra outside
      have bound : degree - 1 - 2 * (offset : ℤ) < 0 := by
        simp only [Finset.mem_coe, Finset.mem_range, not_lt] at outside
        omega
      exact member (by simp [creationDerivativeTerm, halfCreationCoeff, bound])
    rw [finsum_eq_sum_of_support_subset _ contained]
    have coefficient : halfCreationCoeff D charge degree =
        PowerSeries.coeff ((degree - 1).toNat + 1) (halfCreationExponential D charge) := by
      simp only [halfCreationCoeff, if_neg (by omega : ¬ degree < 0)]
      rw [show degree.toNat = (degree - 1).toNat + 1 by omega]
    rw [coefficient]
    have factor : (degree : ℂ) / 2 = (1 / 2 : ℂ) * ((degree - 1).toNat + 1 : ℂ) := by
      have cast : (degree : ℂ) = ((degree - 1).toNat + 1 : ℂ) := by exact_mod_cast natural
      rw [cast]
      ring
    rw [factor, mul_smul, differentiated, smul_smul]
    norm_num
  · have allZero : creationDerivativeTerm D charge degree = 0 := by
      funext offset
      simp [creationDerivativeTerm, halfCreationCoeff,
        show degree - 1 - 2 * (offset : ℤ) < 0 by omega]
    rw [allZero]
    by_cases zero : degree = 0
    · subst degree
      simp
    · simp [halfCreationCoeff, show degree < 0 by omega]

private theorem ground_left_term (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : ℤ) (ground : ActualGround D hu) (offset : ℕ) :
    leftTerm D hu (fun colour => (charge colour : ℂ)) charge exponent 0
      ((1 : Oscillator D) ⊗ₜ[ℂ] ground) offset =
      chargeScalar D charge •
        (creationDerivativeTerm D charge (exponent + chargeNorm D charge + 2) offset ⊗ₜ[ℂ]
          groundAction D hu charge ground) := by
  simp only [leftTerm, zero_sub, charged_vacuum_coefficient, currentCombination,
    Finset.sum_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_smul]
  rw [show -(1 : ℤ) - offset = -(offset : ℤ) - 1 by omega]
  simp only [tensorCurrent, tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply,
    current_negative, LinearMap.mulLeft_apply, TensorProduct.smul_tmul']
  congr 1
  rw [← TensorProduct.sum_tmul]
  congr 1
  rw [show exponent + 2 * 0 + 1 - 2 * offset + chargeNorm D charge =
      exponent + chargeNorm D charge + 2 - 1 - 2 * offset by omega]
  simp only [creationDerivativeTerm, Finset.sum_mul, smul_mul_assoc,
    TensorProduct.smul_tmul']

private theorem ground_right_term (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : ℤ) (ground : ActualGround D hu) (offset : ℕ) :
    rightTerm D hu (fun colour => (charge colour : ℂ)) charge exponent 0
      ((1 : Oscillator D) ⊗ₜ[ℂ] ground) offset = 0 := by
  have currentZero : currentCombination D hu (fun colour => (charge colour : ℂ))
      (0 + offset) ((1 : Oscillator D) ⊗ₜ[ℂ] ground) = 0 := by
    have vanished (colour : Fin D.rank) : current D colour offset (1 : Oscillator D) = 0 :=
      current_vanish D colour 1 _ (by simp [bound])
    simp [currentCombination, tensorCurrent, tensorEnd, vanished]
  simp only [rightTerm, currentZero, map_zero]

private theorem charge_pairing_self (D : LatticeData) (charge : Charge D) :
    chargePairing D (fun colour => (charge colour : ℂ)) charge =
      (chargeNorm D charge : ℂ) := by
  simp [chargePairing, chargeNorm, bilinear, unitCharge, Int.cast_sum,
    Finset.mul_sum, mul_assoc]

theorem original_ground_translation_physical (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : ℤ) (ground : ActualGround D hu) :
    (Ytw D hu (LatticeSugawaraConformal.translation D (Finsupp.single charge 1))).coeff
        exponent ((1 : Oscillator D) ⊗ₜ[ℂ] ground) =
      (((exponent + 2 : ℤ) : ℂ) / 2) •
        (Ytw D hu (Finsupp.single charge 1)).coeff (exponent + 2)
          ((1 : Oscillator D) ⊗ₜ[ℂ] ground) := by
  have sourceIdentity : LatticeSugawaraConformal.translation D (Finsupp.single charge 1) =
      originalFirstDescendant D (fun colour => (charge colour : ℂ)) charge := by
    simp [LatticeSugawaraConformal.translation_single, LatticeSugawaraConformal.chargePolynomial,
      originalFirstDescendant, Finsupp.single_finsetSum, Finsupp.smul_single]
  rw [sourceIdentity, Ytw_charge]
  change _ = (((exponent + 2 : ℤ) : ℂ) / 2) •
    chargedCoefficient D hu charge (exponent + 2) ((1 : Oscillator D) ⊗ₜ[ℂ] ground)
  have descendant := native_first_descendant_mixed_iterate D hu
    (fun colour => (charge colour : ℂ)) charge exponent 0 ((1 : Oscillator D) ⊗ₜ[ℂ] ground)
  simp only [Int.cast_zero, zero_add, charge_pairing_self, ground_left_term,
    ground_right_term, finsum_zero, add_zero] at descendant
  let tensorMap : Oscillator D →ₗ[ℂ] ActualTensor D hu :=
    chargeScalar D charge •
      (TensorProduct.mk ℂ (Oscillator D) (ActualGround D hu)).flip (groundAction D hu charge ground)
  have summed := tensorMap.toAddMonoidHom.map_finsum
    (creationDerivativeTerm_finite D charge (exponent + chargeNorm D charge + 2))
  change tensorMap (∑ᶠ offset : ℕ,
      creationDerivativeTerm D charge (exponent + chargeNorm D charge + 2) offset) =
    (∑ᶠ offset : ℕ, chargeScalar D charge •
      (creationDerivativeTerm D charge (exponent + chargeNorm D charge + 2) offset ⊗ₜ[ℂ]
        groundAction D hu charge ground)) at summed
  rw [← summed, ← creation_physical_recurrence, map_smul] at descendant
  have vacuum := charged_vacuum_coefficient D hu charge (exponent + 2) ground
  have shifted : exponent + 2 + chargeNorm D charge =
      exponent + chargeNorm D charge + 2 := by omega
  rw [shifted] at vacuum
  change chargedCoefficient D hu charge (exponent + 2) ((1 : Oscillator D) ⊗ₜ[ℂ] ground) =
    tensorMap (halfCreationCoeff D charge (exponent + chargeNorm D charge + 2)) at vacuum
  rw [← vacuum] at descendant
  have scalar : (((exponent + chargeNorm D charge + 2 : ℤ) : ℂ) / 2) =
      (((exponent + 2 : ℤ) : ℂ) / 2) + (1 / 2 : ℂ) * (chargeNorm D charge : ℂ) := by
    push_cast
    ring
  rw [scalar, add_smul] at descendant
  exact add_right_cancel descendant

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedTranslation

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockChargedTranslation.original_ground_translation_physical
