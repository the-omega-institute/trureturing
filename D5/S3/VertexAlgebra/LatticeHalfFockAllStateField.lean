/- GID: D5/S3/VertexAlgebra/LatticeHalfFockAllStateField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockAllStateField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite corrected native fields on the complete ordinary lattice carrier. -/

import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
import D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockAllStateField

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFiniteCorrection LatticeHalfFockFockNormalField

noncomputable section

def correctedPolynomial (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D) :
    Oscillator D →ₗ[ℂ] NativeField D hu :=
  (Finsupp.lsum ℂ (fun shift : ℕ =>
    (shiftLinear D hu shift).comp (normalPolynomial D hu charge))).comp (Corr D charge)

def Ytw (D : LatticeData) (hu : IsUnit D.G.det) :
    Carrier D →ₗ[ℂ] NativeField D hu :=
  Finsupp.lsum ℂ (correctedPolynomial D hu)

def correctedWord (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (word : List (Index D)) : NativeField D hu :=
  Finsupp.lsum ℂ (fun shift : ℕ =>
    (shiftLinear D hu shift).comp (normalPolynomial D hu charge))
      (shiftCoefficients D (MvPolynomial.optionEquivLeft ℂ (Index D) (correctionWord D charge word)))

theorem Ytw_monomial_enumeration (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : Index D →₀ ℕ) (word : List (Index D))
    (enumeration : word.Perm (LatticeAllStateField.occurrences D exponent)) :
    Ytw D hu (Finsupp.single charge (MvPolynomial.monomial exponent 1)) =
      correctedWord D hu charge word := by
  simp only [Ytw, Finsupp.lsum_single, correctedPolynomial, LinearMap.comp_apply]
  rw [Corr_monomial_enumeration D charge exponent word enumeration]
  rfl

theorem Ytw_charge (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D) :
    Ytw D hu (Finsupp.single charge 1) = chargedField D hu charge := by
  simp only [Ytw, Finsupp.lsum_single, correctedPolynomial, LinearMap.comp_apply,
    Corr_one, Finsupp.lsum_single, normalPolynomial_one, shiftLinear_zero]

theorem Ytw_vacuum (D : LatticeData) (hu : IsUnit D.G.det) :
    Ytw D hu (Finsupp.single 0 1) = FieldNormalProduct.identityField := by
  rw [Ytw_charge, charged_zero_identity]

theorem Ytw_current_insertion (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) :
    Ytw D hu (Finsupp.single 0 (MvPolynomial.X index)) =
      normalInsertion D hu index FieldNormalProduct.identityField := by
  simp only [Ytw, Finsupp.lsum_single, correctedPolynomial, LinearMap.comp_apply,
    Corr_X_zero, Finsupp.lsum_single, normalPolynomial_X, shiftLinear_zero,
    charged_zero_identity]

theorem Ytw_current (D : LatticeData) (hu : IsUnit D.G.det) (colour : Fin D.rank) :
    Ytw D hu (Finsupp.single 0 (MvPolynomial.X (colour, 0))) =
      LatticeHalfFock.tensorCurrentField D (ActualGround D hu) colour := by
  rw [Ytw_current_insertion, normalInsertion_identity_current]

def sourceWeightBound (D : LatticeData) (state : Carrier D) : ℕ :=
  state.support.sup (fun charge =>
    MvPolynomial.weightedTotalDegree (sourceWeight D) (state charge))

def correctedOrders (D : LatticeData) (hu : IsUnit D.G.det)
    (state : Carrier D) (vector : ActualTensor D hu) : Finset ℤ :=
  state.support.biUnion (fun charge => (Corr D charge (state charge)).support.image
    (fun shift => ((HahnModule.of ℂ).symm
      (normalPolynomial D hu charge (Corr D charge (state charge) shift) vector)).order))

def coefficientOrderMinimum (D : LatticeData) (hu : IsUnit D.G.det)
    (state : Carrier D) (vector : ActualTensor D hu) : ℤ :=
  (insert 0 (correctedOrders D hu state vector)).min' (by simp)

private theorem Ytw_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (state : Carrier D) :
    Ytw D hu state = ∑ charge ∈ state.support,
      ∑ shift ∈ (Corr D charge (state charge)).support,
        shiftLinear D hu shift (normalPolynomial D hu charge (Corr D charge (state charge) shift)) := by
  simp only [Ytw, correctedPolynomial, Finsupp.lsum_apply, Finsupp.sum,
    LinearMap.comp_apply]

theorem Ytw_enumerated_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (state : Carrier D)
    (words : Charge D → ℕ → (Index D →₀ ℕ) → List (Index D))
    (enumeration : ∀ charge shift exponent,
      (words charge shift exponent).Perm (LatticeAllStateField.occurrences D exponent)) :
    Ytw D hu state = ∑ charge ∈ state.support,
      ∑ shift ∈ (Corr D charge (state charge)).support,
        ∑ exponent ∈ (Corr D charge (state charge) shift).support,
          MvPolynomial.coeff exponent (Corr D charge (state charge) shift) •
            shiftLinear D hu shift (normalWord D hu charge (words charge shift exponent)) := by
  classical
  rw [Ytw_expansion]
  apply Finset.sum_congr rfl
  intro charge chargeMember
  apply Finset.sum_congr rfl
  intro shift shiftMember
  rw [normalPolynomial_enumerated_expansion D hu charge _ (words charge shift)
    (fun exponent _ => enumeration charge shift exponent)]
  simp only [map_sum, map_smul]

theorem Ytw_fock_normal_coefficients (D : LatticeData) (hu : IsUnit D.G.det)
    (state : Carrier D) (vector : ActualTensor D hu) (exponent : ℤ)
    (words : Charge D → ℕ → (Index D →₀ ℕ) → List (Index D))
    (enumeration : ∀ charge shift monomial,
      (words charge shift monomial).Perm (LatticeAllStateField.occurrences D monomial)) :
    (Ytw D hu state).coeff exponent vector = ∑ charge ∈ state.support,
      ∑ shift ∈ (Corr D charge (state charge)).support,
        ∑ monomial ∈ (Corr D charge (state charge) shift).support,
          MvPolynomial.coeff monomial (Corr D charge (state charge) shift) •
            ∑ᶠ modes : ModeTuple D (words charge shift monomial),
              leftAction D hu (words charge shift monomial) modes
                (chargedCoefficient D hu charge
                  (exponent + 2 * shift + 2 * modeSum D (words charge shift monomial) modes +
                    jetShift D (words charge shift monomial))
                  (rightAction D hu (words charge shift monomial) modes vector)) := by
  classical
  rw [Ytw_enumerated_expansion D hu state words enumeration]
  simp only [map_sum, Finset.sum_apply, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, shiftLinear, shiftField, LinearMap.coe_mk, AddHom.coe_mk,
    HVertexOperator.coeff_of_coeff, Pi.smul_apply, normalWord_flattened,
    flatTerm, flatCoefficient_factorization, Module.End.mul_apply, chargedField]

theorem Ytw_source_lower_truncation (D : LatticeData) (hu : IsUnit D.G.det)
    (state : Carrier D) (vector : ActualTensor D hu) (exponent : ℤ)
    (below : exponent < coefficientOrderMinimum D hu state vector -
      2 * (sourceWeightBound D state : ℤ)) :
    (Ytw D hu state).coeff exponent vector = 0 := by
  classical
  rw [Ytw_expansion]
  simp only [map_sum, Finset.sum_apply, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro charge chargeMember
  apply Finset.sum_eq_zero
  intro shift shiftMember
  have shiftBound := (Corr_shift_bound D charge (state charge) shift shiftMember).trans
    (Finset.le_sup (f := fun charge =>
      MvPolynomial.weightedTotalDegree (sourceWeight D) (state charge)) chargeMember)
  have orderMember : ((HahnModule.of ℂ).symm
      (normalPolynomial D hu charge (Corr D charge (state charge) shift) vector)).order ∈
      insert 0 (correctedOrders D hu state vector) := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_biUnion.mpr ⟨charge, chargeMember,
      Finset.mem_image.mpr ⟨shift, shiftMember, rfl⟩⟩
  have orderBound := Finset.min'_le _ _ orderMember
  change coefficientOrderMinimum D hu state vector ≤ _ at orderBound
  change ((HahnModule.of ℂ).symm
    (normalPolynomial D hu charge (Corr D charge (state charge) shift) vector)).coeff
      (exponent + 2 * shift) = 0
  apply HahnSeries.coeff_eq_zero_of_lt_order
  change shift ≤ sourceWeightBound D state at shiftBound
  omega

end
end D5.S3.VertexAlgebra.LatticeHalfFockAllStateField

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockAllStateField.Ytw_monomial_enumeration
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockAllStateField.Ytw_charge
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockAllStateField.Ytw_vacuum
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockAllStateField.Ytw_current_insertion
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockAllStateField.Ytw_current
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockAllStateField.Ytw_source_lower_truncation
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockAllStateField.Ytw_enumerated_expansion
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockAllStateField.Ytw_fock_normal_coefficients
