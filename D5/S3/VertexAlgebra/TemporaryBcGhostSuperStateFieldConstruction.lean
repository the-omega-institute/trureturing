import D5.S3.VertexAlgebra.TemporaryBcGhostSuperJacobi

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostSuperStateFieldConstruction

open BcGhostFockSupport BcGhostSuperGenerators BcGhostSuperStateField BcGhostSuperLocality
open BcGhostSuperReconstruction BcGhostSuperResidues BcGhostSuperBorcherdsTerms
open BcGhostSuperJacobi FieldNormalProduct SuperFieldProducts
open scoped VertexOperator

noncomputable section

theorem original_b_modes (mode : ℤ) :
    ((Y (b (-2) (vacuum : Carrier)))[[mode]]) = b (mode - 1) := by
  rw [stateField_b_generator, currentField_modes]
  rfl

theorem original_c_modes (mode : ℤ) :
    ((Y (c 1 (vacuum : Carrier)))[[mode]]) = c (mode + 2) := by
  rw [stateField_c_generator, currentField_modes]
  rfl

theorem full_carrier_stateField :
    Y (vacuum : Carrier) = identityField ∧
    (∀ state : Carrier, ((Y state)[[-1]]) (vacuum : Carrier) = state) ∧
    (∀ (state : Carrier) (mode : ℤ), 0 ≤ mode → ((Y state)[[mode]]) (vacuum : Carrier) = 0) ∧
    (∀ state vector : Carrier, ∃ cutoff : ℤ, ∀ mode : ℤ,
      cutoff ≤ mode → ((Y state)[[mode]]) vector = 0) ∧
    translation (vacuum : Carrier) = 0 ∧
    (∀ state : Carrier, Y (translation state) = dividedDerivative 1 (Y state)) ∧
    (∀ (state : Carrier) (mode : ℤ), translation * ((Y state)[[mode]]) -
      ((Y state)[[mode]]) * translation = -(mode : ℂ) • ((Y state)[[mode - 1]])) ∧
    (∀ (parity : ℕ) (state : Carrier), state ∈ homogeneous parity →
      ∀ mode : ℤ, HomogeneousOperator parity (((Y state)[[mode]]))) ∧
    (∀ (leftParity rightParity : ℕ) (left right : Carrier), left ∈ homogeneous leftParity →
      right ∈ homogeneous rightParity → SuperLocal leftParity rightParity (Y left) (Y right)) ∧
    (∀ (leftParity rightParity : ℕ) (left right : Carrier) (parameter : ℤ),
      left ∈ homogeneous leftParity → right ∈ homogeneous rightParity →
      Y (((Y left)[[parameter]]) right) =
        residue (koszul leftParity rightParity) parameter (Y left) (Y right)) ∧
    (∀ (leftParity rightParity : ℕ) (left right vector : Carrier) (first parameter last : ℤ),
      left ∈ homogeneous leftParity → right ∈ homogeneous rightParity →
      BorcherdsEquation leftParity rightParity first parameter last left right vector) ∧
    (∀ (leftParity rightParity : ℕ) (left right vector : Carrier) (first parameter last : ℤ),
      Function.HasFiniteSupport (borcherdsLeftTerm first parameter last left right vector) ∧
        Function.HasFiniteSupport
          (borcherdsRightTerm leftParity rightParity first parameter last left right vector)) ∧
    (∀ (first parameter last : ℤ) (left right vector : Carrier),
      MixedBorcherdsEquation first parameter last left right vector) := by
  refine ⟨stateField_vacuum, stateField_creation, stateField_creativity,
    stateField_lower_truncation, translation_vacuum, stateField_translation, stateField_covariance,
    stateField_mem, stateField_superLocal, stateField_residue_closure, ?_, ?_, mixed_borcherds⟩
  · intro leftParity rightParity left right vector first parameter last leftHomogeneous rightHomogeneous
    exact borcherds leftParity rightParity left right vector leftHomogeneous rightHomogeneous first last parameter
  · intro leftParity rightParity left right vector first parameter last
    exact ⟨borcherds_left_finite first parameter last left right vector,
      borcherds_right_finite leftParity rightParity first parameter last left right vector⟩

theorem mixed_parity_split (state : Carrier) :
    state = parityPart 0 state + parityPart 1 state ∧
      parityPart 0 state ∈ homogeneous 0 ∧ parityPart 1 state ∈ homogeneous 1 ∧
      parityPart 0 (parityPart 0 state) = parityPart 0 state ∧
      parityPart 1 (parityPart 1 state) = parityPart 1 state ∧
      (∀ vector : Carrier, vector ∈ homogeneous 0 → vector ∈ homogeneous 1 → vector = 0) := by
  exact ⟨(parity_decomposition state).symm, parityPart_mem 0 state, parityPart_mem 1 state,
    parityPart_identity 0 _ (parityPart_mem 0 state),
    parityPart_identity 1 _ (parityPart_mem 1 state), homogeneous_intersection_zero⟩

end
end D5.S3.VertexAlgebra.BcGhostSuperStateFieldConstruction
