/- GID: D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockFirstDescendant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual charged first-source-oscillator correction and descendant coefficient.
   proof_shape: Corr_charged_first_oscillator: content
   admission_basis: escape-witness
   escape_witness: The literal original charged first-descendant is expanded through
   the released Corr/Ytw constructor. Its charged correction is not a
   consequence of the zero-charge Corr_X_zero specialization.
   Literature status: classical twisted lattice construction; zero novelty. -/

import D5.S3.VertexAlgebra.LatticeHalfFockAllStateField

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendant

open LatticeGeneratingFieldLocality
open MvPolynomial
open LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFiniteCorrection
open LatticeHalfFockFockNormalField
open LatticeHalfFockAllStateField
open LatticeHalfFock
open scoped BigOperators TensorProduct

noncomputable section

def originalFirstDescendant (D : LatticeData) (h : Fin D.rank → ℂ) (a : Charge D) :
    Carrier D :=
  ∑ colour, h colour • Finsupp.single a (MvPolynomial.X (colour, 0))

def currentCombination (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (mode : ℤ) : Module.End ℂ (ActualTensor D hu) :=
  ∑ colour, h colour • tensorCurrent D (ActualGround D hu) colour mode

def chargePairing (D : LatticeData) (h : Fin D.rank → ℂ) (a : Charge D) : ℂ :=
  ∑ colour, h colour * (bilinear D (unitCharge D colour) a : ℂ)

private theorem correctionWord_zero_singleton (D : LatticeData) (a : Charge D)
    (colour : Fin D.rank) :
    optionEquivLeft ℂ (Index D) (correctionWord D a [(colour, 0)]) =
      Polynomial.C (MvPolynomial.X (colour, 0)) +
        Polynomial.C (((-((bilinear D (unitCharge D colour) a : ℂ) / 2)) : ℂ) •
          (1 : Oscillator D)) * Polynomial.X := by
  have scalar : halfBinomial 1 * (bilinear D (unitCharge D colour) a : ℂ) =
      -((bilinear D (unitCharge D colour) a : ℂ) / 2) := by
    norm_num [halfBinomial]
    ring
  simp [correctionWord, insertion, singletonPolynomial, sourceWeight, scalar,
    MvPolynomial.smul_eq_C_mul]

theorem Corr_charged_first_oscillator (D : LatticeData) (a : Charge D)
    (colour : Fin D.rank) :
    Corr D a (MvPolynomial.X (colour, 0)) =
      Finsupp.single 0 (MvPolynomial.X (colour, 0)) +
        Finsupp.single 1 (-((bilinear D (unitCharge D colour) a : ℂ) / 2) • 1) := by
  have enumeration : [(colour, 0)].Perm
      (LatticeAllStateField.occurrences D (Finsupp.single (colour, 0) 1)) := by
    simp [LatticeAllStateField.occurrences]
  have monomial := Corr_monomial_enumeration D a (Finsupp.single (colour, 0) 1)
    [(colour, 0)] enumeration
  rw [show Corr D a (MvPolynomial.X (colour, 0)) =
      shiftCoefficients D (optionEquivLeft ℂ (Index D) (correctionWord D a [(colour, 0)])) by
        simpa [MvPolynomial.X] using monomial]
  rw [correctionWord_zero_singleton]
  ext shift
  by_cases zero : shift = 0
  · subst shift
    simp [shiftCoefficients]
  · by_cases one : shift = 1
    · subst shift
      simp [shiftCoefficients]
    · simp [shiftCoefficients, zero, one]

theorem charged_first_descendant_field (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (colour : Fin D.rank) :
    Ytw D hu (Finsupp.single a (MvPolynomial.X (colour, 0))) =
      normalInsertion D hu (colour, 0) (chargedField D hu a) -
        ((bilinear D (unitCharge D colour) a : ℂ) / 2) • shiftLinear D hu 1
          (chargedField D hu a) := by
  simp only [Ytw, Finsupp.lsum_single, correctedPolynomial, LinearMap.comp_apply]
  rw [Corr_charged_first_oscillator, map_add]
  simp only [Finsupp.lsum_single]
  simp [normalPolynomial_X, normalPolynomial_one, shiftLinear_zero]
  module

theorem originalFirstDescendant_field (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (a : Charge D) :
    Ytw D hu (originalFirstDescendant D h a) =
      ∑ colour, h colour •
        (normalInsertion D hu (colour, 0) (chargedField D hu a) -
          ((bilinear D (unitCharge D colour) a : ℂ) / 2) •
            shiftLinear D hu 1 (chargedField D hu a)) := by
  simp only [originalFirstDescendant, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro colour hcolour
  rw [charged_first_descendant_field]

theorem originalFirstDescendant_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (a : Charge D) (exponent : ℤ) (vector : ActualTensor D hu) :
    (Ytw D hu (originalFirstDescendant D h a)).coeff exponent vector =
      (∑ colour, h colour •
        (normalInsertion D hu (colour, 0) (chargedField D hu a)).coeff exponent vector) -
      (chargePairing D h a / 2) •
        chargedCoefficient D hu a (exponent + 2) vector := by
  rw [originalFirstDescendant_field]
  change (HVertexOperator.coeff
      (∑ colour, h colour •
        (normalInsertion D hu (colour, 0) (chargedField D hu a) -
          ((bilinear D (unitCharge D colour) a : ℂ) / 2) •
            shiftLinear D hu 1 (chargedField D hu a))) exponent) vector = _
  rw [map_sum]
  simp only [Finset.sum_apply, LinearMap.sum_apply, map_sub, map_smul,
    Pi.sub_apply, Pi.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  simp only [shiftLinear, chargedField, smul_sub, smul_smul, Finset.sum_sub_distrib]
  congr 1
  rw [chargePairing, Finset.sum_div, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro colour member
  congr 1
  ring

end
end D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendant

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendant.Corr_charged_first_oscillator
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendant.charged_first_descendant_field
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendant.originalFirstDescendant_coefficient
