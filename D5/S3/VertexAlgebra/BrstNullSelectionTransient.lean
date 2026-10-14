import D5.S3.VertexAlgebra.BrstFramePrimitivesTransient

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open Module LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open scoped BigOperators

noncomputable section

def originalGramForm (D : LatticeData) :
    LinearMap.BilinForm ℂ (Fin D.rank → ℂ) :=
  Matrix.toBilin' (gramComplex D)

theorem originalGramForm_apply (D : LatticeData) (left right : Fin D.rank → ℂ) :
    originalGramForm D left right = gramPair D left right := by
  rw [originalGramForm, Matrix.toBilin'_apply]
  rfl

theorem originalGramForm_symmetric (D : LatticeData) :
    LinearMap.BilinForm.IsSymm (originalGramForm D) := by
  refine ⟨?_⟩
  intro left right
  simpa only [originalGramForm_apply] using gramPair_symm D left right

theorem originalGramForm_nondegenerate (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1)
    (rightInverse : gramComplex D * H = 1) :
    (originalGramForm D).Nondegenerate := by
  have leftDeterminant : (gramComplex D).det ≠ 0 :=
    Matrix.det_ne_zero_of_left_inverse leftInverse
  have rightDeterminant : (gramComplex D).det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse rightInverse
  have leftNondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
      (gramComplex D) leftDeterminant
  have rightNondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
      (gramComplex D) rightDeterminant
  exact ⟨leftNondegenerate.1, rightNondegenerate.2⟩

theorem original_complexCharge_ne_zero (D : LatticeData) (charge : Charge D)
    (chargeNonzero : charge ≠ 0) : complexCharge D charge ≠ 0 := by
  intro complexZero
  apply chargeNonzero
  funext index
  have coordinateZero : (charge index : ℂ) = 0 := congr_fun complexZero index
  exact_mod_cast coordinateZero

theorem original_nonzero_charge_null_selection (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1)
    (rightInverse : gramComplex D * H = 1)
    (rankAtLeastTwo : 2 ≤ D.rank) (charge : Charge D)
    (chargeNonzero : charge ≠ 0) :
    ∃ nullDirection : Fin D.rank → ℂ,
      gramPair D nullDirection nullDirection = 0 ∧
      chosenP D charge nullDirection ≠ 0 := by
  classical
  let form := originalGramForm D
  let chargedVector := complexCharge D charge
  have formNondegenerate : form.Nondegenerate :=
    originalGramForm_nondegenerate D H leftInverse rightInverse
  have formSymmetric : LinearMap.IsSymm form :=
    (LinearMap.BilinForm.isSymm_iff).mp (originalGramForm_symmetric D)
  have chargedVectorNonzero : chargedVector ≠ 0 :=
    original_complexCharge_ne_zero D charge chargeNonzero
  obtain ⟨orthogonalBasis, orthogonality⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis formSymmetric
  have dimension : Module.finrank ℂ (Fin D.rank → ℂ) = D.rank :=
    Module.finrank_fin_fun ℂ
  have dimensionAtLeastTwo : 2 ≤ Module.finrank ℂ (Fin D.rank → ℂ) := by
    simpa only [dimension] using rankAtLeastTwo
  obtain ⟨selectedIndex, selectedPairNonzero⟩ :
      ∃ index, form (orthogonalBasis index) chargedVector ≠ 0 := by
    by_contra noIndex
    push_neg at noIndex
    have zeroFunctional : form.flip chargedVector = 0 := by
      apply orthogonalBasis.ext
      intro index
      exact noIndex index
    apply chargedVectorNonzero
    apply formNondegenerate.2 chargedVector
    intro vector
    exact congrArg (fun functional : (Fin D.rank → ℂ) →ₗ[ℂ] ℂ => functional vector)
      zeroFunctional
  let zeroIndex : Fin (Module.finrank ℂ (Fin D.rank → ℂ)) := ⟨0, by omega⟩
  let oneIndex : Fin (Module.finrank ℂ (Fin D.rank → ℂ)) := ⟨1, by omega⟩
  have zeroOneDistinct : zeroIndex ≠ oneIndex := by
    simp [zeroIndex, oneIndex]
  obtain ⟨otherIndex, otherDistinct⟩ : ∃ index, index ≠ selectedIndex := by
    by_cases selectedZero : selectedIndex = zeroIndex
    · exact ⟨oneIndex, by simpa only [selectedZero] using zeroOneDistinct.symm⟩
    · exact ⟨zeroIndex, Ne.symm selectedZero⟩
  have selectedOtherZero :
      form (orthogonalBasis selectedIndex) (orthogonalBasis otherIndex) = 0 :=
    by
      apply orthogonality
      exact Ne.symm otherDistinct
  have otherSelectedZero :
      form (orthogonalBasis otherIndex) (orthogonalBasis selectedIndex) = 0 :=
    by
      apply orthogonality
      exact otherDistinct
  have otherNormNonzero :
      form (orthogonalBasis otherIndex) (orthogonalBasis otherIndex) ≠ 0 :=
    orthogonality.not_isOrtho_basis_self_of_separatingLeft formNondegenerate.1 otherIndex
  obtain ⟨root, rootEquation⟩ := IsAlgClosed.exists_eq_mul_self
    (-form (orthogonalBasis selectedIndex) (orthogonalBasis selectedIndex) /
      form (orthogonalBasis otherIndex) (orthogonalBasis otherIndex))
  have rootCancellation :
      root * root * form (orthogonalBasis otherIndex) (orthogonalBasis otherIndex) =
        -form (orthogonalBasis selectedIndex) (orthogonalBasis selectedIndex) := by
    rw [← rootEquation, div_mul_cancel₀ _ otherNormNonzero]
  have nullCombination (scalar : ℂ)
      (scalarEquation :
        scalar * scalar * form (orthogonalBasis otherIndex) (orthogonalBasis otherIndex) =
          -form (orthogonalBasis selectedIndex) (orthogonalBasis selectedIndex)) :
      form (orthogonalBasis selectedIndex + scalar • orthogonalBasis otherIndex)
        (orthogonalBasis selectedIndex + scalar • orthogonalBasis otherIndex) = 0 := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      selectedOtherZero, otherSelectedZero, mul_zero, add_zero, zero_add]
    calc
      _ = form (orthogonalBasis selectedIndex) (orthogonalBasis selectedIndex) +
          scalar * scalar * form (orthogonalBasis otherIndex) (orthogonalBasis otherIndex) := by
        ring
      _ = 0 := by rw [scalarEquation]; ring
  have positiveNull := nullCombination root rootCancellation
  have negativeNull := nullCombination (-root) (by simpa using rootCancellation)
  by_cases positivePair :
      form (orthogonalBasis selectedIndex + root • orthogonalBasis otherIndex) chargedVector ≠ 0
  · refine ⟨orthogonalBasis selectedIndex + root • orthogonalBasis otherIndex, ?_, ?_⟩
    · simpa only [form, originalGramForm_apply] using positiveNull
    · simpa only [form, chargedVector, originalGramForm_apply, chosenP] using positivePair
  · have positiveZero :
        form (orthogonalBasis selectedIndex + root • orthogonalBasis otherIndex) chargedVector = 0 :=
      not_ne_iff.mp positivePair
    refine ⟨orthogonalBasis selectedIndex + (-root) • orthogonalBasis otherIndex, ?_, ?_⟩
    · simpa only [form, originalGramForm_apply] using negativeNull
    · have negativePair :
          form (orthogonalBasis selectedIndex + (-root) • orthogonalBasis otherIndex)
            chargedVector ≠ 0 := by
        intro negativeZero
        have sumZero : (2 : ℂ) * form (orthogonalBasis selectedIndex) chargedVector = 0 := by
          calc
            _ = form (orthogonalBasis selectedIndex + root • orthogonalBasis otherIndex) chargedVector +
                form (orthogonalBasis selectedIndex + (-root) • orthogonalBasis otherIndex)
                  chargedVector := by
              simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left]
              ring
            _ = 0 := by rw [positiveZero, negativeZero]; ring
        exact selectedPairNonzero ((mul_eq_zero.mp sumZero).resolve_left (by norm_num))
      simpa only [form, chargedVector, originalGramForm_apply, chosenP] using negativePair

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
