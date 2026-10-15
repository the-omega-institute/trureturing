/- GID: D5/S3/VertexAlgebra/LatticeHalfFockCorrectedCurrentAction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockCorrectedCurrentAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual current action on full charged corrected native polynomial fields. -/

import D5.S3.VertexAlgebra.LatticeHalfFockNormalCurrentCommutator
import D5.S3.VertexAlgebra.LatticeHalfFockAllStateField

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockCorrectedCurrentAction

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFiniteCorrection
open LatticeHalfFockFockNormalField LatticeHalfFockAllStateField
open LatticeHalfFockCurrentNormalRecurrence LatticeHalfFockNormalCurrentAction
open LatticeHalfFockNormalCurrentCommutator
open scoped BigOperators

noncomputable section

private theorem Corr_mode_support (D : LatticeData) (charge : Charge D)
    (colour : Fin D.rank) (degree : ℕ) (polynomial : Oscillator D) :
    (Corr D charge (neutralPolynomialMode D colour charge degree polynomial)).support ⊆
      (Corr D charge polynomial).support := by
  intro shift member
  by_contra outside
  have zero : Corr D charge polynomial shift = 0 := Finsupp.notMem_support_iff.mp outside
  have vanish : Corr D charge (neutralPolynomialMode D colour charge degree polynomial) shift = 0 := by
    rw [Corr_neutralPolynomialMode, zero, map_zero]
  exact Finsupp.mem_support_iff.mp member vanish

private theorem correctedPolynomial_sum_on (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Oscillator D) (shifts : Finset ℕ)
    (support : (Corr D charge polynomial).support ⊆ shifts) :
    correctedPolynomial D hu charge polynomial = ∑ shift ∈ shifts,
      shiftLinear D hu shift (normalPolynomial D hu charge (Corr D charge polynomial shift)) := by
  classical
  simp only [correctedPolynomial, LinearMap.comp_apply, Finsupp.lsum_apply, Finsupp.sum]
  apply Finset.sum_subset support
  intro shift member outside
  simp [Finsupp.notMem_support_iff.mp outside]

private theorem deltaTerm_Corr_support (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (colour : Fin D.rank) (mode : ℤ) (polynomial : Oscillator D)
    (shift : ℕ) :
    Function.support (deltaTerm D hu charge colour mode (Corr D charge polynomial shift)) ⊆
      Finset.range (polynomialFrequencyBound D polynomial + 1) := by
  intro degree nonzero
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra outside
  have vanish := neutralPolynomialMode_vanish D colour charge polynomial degree (by omega)
  have correctedVanish :
      neutralPolynomialMode D colour charge degree (Corr D charge polynomial shift) = 0 := by
    rw [← Corr_neutralPolynomialMode, vanish, map_zero, Finsupp.zero_apply]
  exact nonzero (by simp [deltaTerm, correctedVanish])

private theorem coverShift_shiftLinear (D : LatticeData) (hu : IsUnit D.G.det)
    (shift : ℤ) (correctionShift : ℕ) (field : NativeField D hu) :
    coverShiftLinear D hu shift (shiftLinear D hu correctionShift field) =
      shiftLinear D hu correctionShift (coverShiftLinear D hu shift field) := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  simp only [coverShiftLinear, coverShift, shiftLinear, shiftField,
    LinearMap.coe_mk, AddHom.coe_mk, HVertexOperator.coeff_of_coeff]
  rw [show exponent + shift + 2 * (correctionShift : ℤ) =
    exponent + 2 * correctionShift + shift by omega]

def correctedDeltaTerm (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (colour : Fin D.rank) (mode : ℤ) (polynomial : Oscillator D) (degree : ℕ) :
    NativeField D hu :=
  Ring.choose (LatticeHalfFock.frequency mode) degree •
    coverShiftLinear D hu (-(2 * mode + 1) + 2 * degree)
      (correctedPolynomial D hu charge (neutralPolynomialMode D colour charge degree polynomial))

theorem correctedDeltaTerm_support (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (colour : Fin D.rank) (mode : ℤ) (polynomial : Oscillator D) :
    Function.support (correctedDeltaTerm D hu charge colour mode polynomial) ⊆
      Finset.range (polynomialFrequencyBound D polynomial + 1) := by
  intro degree nonzero
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra outside
  have vanish := neutralPolynomialMode_vanish D colour charge polynomial degree (by omega)
  exact nonzero (by simp [correctedDeltaTerm, vanish])

def correctedDelta (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (colour : Fin D.rank) (mode : ℤ) (polynomial : Oscillator D) : NativeField D hu :=
  ∑ᶠ degree : ℕ, correctedDeltaTerm D hu charge colour mode polynomial degree

private theorem correctedDelta_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (colour : Fin D.rank) (mode : ℤ) (polynomial : Oscillator D) :
    correctedDelta D hu charge colour mode polynomial =
      ∑ shift ∈ (Corr D charge polynomial).support,
        shiftLinear D hu shift
          (nativeDelta D hu charge colour mode (Corr D charge polynomial shift)) := by
  classical
  rw [correctedDelta, finsum_eq_sum_of_support_subset _
    (correctedDeltaTerm_support D hu charge colour mode polynomial)]
  conv_rhs =>
    enter [2, shift]
    rw [nativeDelta, finsum_eq_sum_of_support_subset _
      (deltaTerm_Corr_support D hu charge colour mode polynomial shift)]
  simp only [map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro degree degreeMember
  rw [correctedDeltaTerm, correctedPolynomial_sum_on D hu charge _
    (Corr D charge polynomial).support (Corr_mode_support D charge colour degree polynomial)]
  simp only [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro shift shiftMember
  rw [Corr_neutralPolynomialMode, coverShift_shiftLinear]
  simp only [deltaTerm, map_smul]

theorem correctedPolynomial_current_commutator (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (colour : Fin D.rank) (mode exponent : ℤ)
    (polynomial : Oscillator D) :
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode *
        (correctedPolynomial D hu charge polynomial).coeff exponent -
      (correctedPolynomial D hu charge polynomial).coeff exponent *
        LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode =
      (correctedDelta D hu charge colour mode polynomial).coeff exponent := by
  classical
  rw [correctedPolynomial_sum_on D hu charge polynomial _ (fun _ member => member),
    correctedDelta_expansion]
  simp only [map_sum, Finset.sum_apply, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro shift member
  simp only [shiftLinear, shiftField, LinearMap.coe_mk, AddHom.coe_mk,
    HVertexOperator.coeff_of_coeff]
  exact normalPolynomial_current_commutator D hu charge colour mode _ _

end
end D5.S3.VertexAlgebra.LatticeHalfFockCorrectedCurrentAction
