/- GID: D5/S3/VertexAlgebra/LatticeHalfFockOriginalMixedIterate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockOriginalMixedIterate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal original-current minus-one mixed iterate under native Ytw.
   Literature status: classical twisted lattice construction; zero novelty. -/

import D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendantCuts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockOriginalMixedIterate

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockAllStateField
open LatticeHalfFockFirstDescendant LatticeHalfFockFirstDescendantCuts
open scoped BigOperators VertexOperator

noncomputable section

def sourceCurrent (D : LatticeData) (h : Fin D.rank → ℂ) : VertexOperator ℂ (Carrier D) :=
  LatticeAllStateField.Y D (originalFirstDescendant D h 0)

private theorem sourceCurrent_field (D : LatticeData) (h : Fin D.rank → ℂ) :
    sourceCurrent D h = ∑ colour, h colour • neutralField D colour := by
  simp only [sourceCurrent, originalFirstDescendant, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro colour member
  have current : ((neutralField D colour)[[-1]]) (LatticeAllStateField.vacuum D) =
      Finsupp.single (0 : Charge D) (MvPolynomial.X (colour, 0) : Oscillator D) := by
    rw [LatticeSugawaraCurrents.neutralField_ncoeff]
    simp [neutralMode, neutralPolynomialMode, LatticeAllStateField.vacuum]
  rw [← current, LatticeAllStateField.stateField_current]

private theorem sourceCurrent_mode (D : LatticeData) (h : Fin D.rank → ℂ) (mode : ℤ) :
    (sourceCurrent D h)[[mode]] = ∑ colour, h colour • neutralMode D colour mode := by
  rw [sourceCurrent_field]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    LatticeSugawaraCurrents.neutralField_ncoeff]

private theorem sourceCurrent_minus_one (D : LatticeData) (h : Fin D.rank → ℂ) (a : Charge D) :
    ((sourceCurrent D h)[[-1]]) (Finsupp.single a 1) = originalFirstDescendant D h a := by
  rw [sourceCurrent_mode]
  simp [originalFirstDescendant, LinearMap.sum_apply, neutralMode, neutralPolynomialMode]

private theorem sourceCurrent_zero (D : LatticeData) (h : Fin D.rank → ℂ) (a : Charge D) :
    ((sourceCurrent D h)[[0]]) (Finsupp.single a 1) =
      chargePairing D h a • Finsupp.single a 1 := by
  rw [sourceCurrent_mode]
  simp [chargePairing, Finset.sum_smul, smul_smul, LinearMap.sum_apply,
    neutralMode, neutralPolynomialMode, Finsupp.smul_single]

private theorem sourceCurrent_positive (D : LatticeData) (h : Fin D.rank → ℂ)
    (a : Charge D) (mode : ℤ) (positive : 1 ≤ mode) :
    ((sourceCurrent D h)[[mode]]) (Finsupp.single a 1) = 0 := by
  rw [sourceCurrent_mode]
  simp [LinearMap.sum_apply, neutralMode, neutralPolynomialMode,
    show ¬mode < 0 by omega, show mode ≠ 0 by omega, LinearMap.sum_apply]

theorem sourceCurrent_ground_modes (D : LatticeData) (h : Fin D.rank → ℂ) (a : Charge D) :
    ((sourceCurrent D h)[[-1]]) (Finsupp.single a 1) = originalFirstDescendant D h a ∧
      ((sourceCurrent D h)[[0]]) (Finsupp.single a 1) =
        chargePairing D h a • Finsupp.single a 1 ∧
      ∀ mode : ℤ, 1 ≤ mode → ((sourceCurrent D h)[[mode]]) (Finsupp.single a 1) = 0 :=
  ⟨sourceCurrent_minus_one D h a, sourceCurrent_zero D h a,
    sourceCurrent_positive D h a⟩

theorem original_mixed_iterate_minus_one (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (a : Charge D) (exponent cut : ℤ) (vector : ActualTensor D hu) :
    (Ytw D hu (((sourceCurrent D h)[[-1]]) (Finsupp.single a 1))).coeff exponent vector +
      ((cut : ℂ) + 1 / 2) •
        (Ytw D hu (((sourceCurrent D h)[[0]]) (Finsupp.single a 1))).coeff
          (exponent + 2) vector =
      (∑ᶠ offset : ℕ, leftTerm D hu h a exponent cut vector offset) +
        ∑ᶠ offset : ℕ, rightTerm D hu h a exponent cut vector offset := by
  obtain ⟨minusOne, zeroMode, higher⟩ := sourceCurrent_ground_modes D h a
  rw [minusOne, zeroMode]
  simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, Ytw_charge,
    chargedField, HVertexOperator.coeff_of_coeff, smul_smul]
  exact native_first_descendant_mixed_iterate D hu h a exponent cut vector

end
end D5.S3.VertexAlgebra.LatticeHalfFockOriginalMixedIterate

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockOriginalMixedIterate.original_mixed_iterate_minus_one
