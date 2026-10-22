/- GID: D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields
   generality: I
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual quotient state fields, vacuum, and translation for the original BRST charge. -/

import D5.S3.VertexAlgebra.LatticeBcGhostCohomologyJacobi

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeBcGhostCohomologyFields

open LatticeGeneratingFieldLocality
open LatticeBcGhostBrstCharge (State Q)
open LatticeBcGhostNeutralCohomology (OriginalCycles OriginalBoundaries OriginalCohomology)
open LatticeBcGhostCohomologyModes
open scoped VertexOperator

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

def field (state : OriginalCohomology D H) : VertexOperator ℂ (OriginalCohomology D H) :=
  VertexOperator.of_coeff (fun degree => product D H (-degree - 1) state) (fun input => by
    obtain ⟨bound, high⟩ := product_lower_truncation D H state input
    refine ⟨-bound - 1, ?_⟩
    intro degree nonzero
    by_contra below
    exact nonzero (high (-degree - 1) (by omega)))

theorem field_mode (state : OriginalCohomology D H) (mode : ℤ) :
    ((field D H state)[[mode]]) = product D H mode state := by
  simp only [field, VertexOperator.ncoeff_of_coeff,
    show -(-mode - 1) - 1 = mode by omega]

def stateField : OriginalCohomology D H →ₗ[ℂ] VertexOperator ℂ (OriginalCohomology D H) where
  toFun := field D H
  map_add' first second := by
    apply HVertexOperator.coeff_inj
    ext degree input
    simp only [map_add, Pi.add_apply, LinearMap.add_apply,
      VertexOperator.coeff_eq_ncoeff, field_mode]
  map_smul' scalar state := by
    apply HVertexOperator.coeff_inj
    ext degree input
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply,
      VertexOperator.coeff_eq_ncoeff, field_mode, RingHom.id_apply]

def cycleVacuum : OriginalCycles D H :=
  ⟨LatticeBcGhostTensorStateField.vacuum D, LatticeBcGhostBrstCurrent.Q_vacuum D H⟩

def vacuum : OriginalCohomology D H := (OriginalBoundaries D H).mkQ (cycleVacuum D H)

theorem creation (state : OriginalCohomology D H) : product D H (-1) state (vacuum D H) = state := by
  obtain ⟨representative, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective state
  rw [vacuum, product_mk]
  congr 1
  apply Subtype.ext
  exact LatticeBcGhostTensorStateField.stateField_creation D representative.val

theorem creativity (state : OriginalCohomology D H) (mode : ℤ) (nonnegative : 0 ≤ mode) :
    product D H mode state (vacuum D H) = 0 := by
  obtain ⟨representative, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective state
  rw [vacuum, product_mk]
  have zero : cycleMode D H mode representative (cycleVacuum D H) = 0 := by
    apply Subtype.ext
    exact LatticeBcGhostTensorStateField.stateField_creativity D representative.val mode nonnegative
  rw [zero, map_zero]

theorem vacuum_product (state : OriginalCohomology D H) (mode : ℤ) :
    product D H mode (vacuum D H) state = if mode = -1 then state else 0 := by
  obtain ⟨representative, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective state
  rw [vacuum, product_mk]
  have raw := LatticeBcGhostTensorStateField.stateField_vacuum D
  by_cases chosen : mode = -1
  · rw [if_pos chosen]
    congr 1
    apply Subtype.ext
    change ((LatticeBcGhostTensorStateField.stateField D
      (LatticeBcGhostTensorStateField.vacuum D))[[mode]]) representative.val = representative.val
    rw [raw, VertexOperatorTensorProduct.identityField_mode]
    simp [chosen]
  · rw [if_neg chosen]
    have zero : cycleMode D H mode (cycleVacuum D H) representative = 0 := by
      apply Subtype.ext
      change ((LatticeBcGhostTensorStateField.stateField D
        (LatticeBcGhostTensorStateField.vacuum D))[[mode]]) representative.val = 0
      rw [raw, VertexOperatorTensorProduct.identityField_mode]
      simp [chosen]
    rw [zero, map_zero]

theorem Q_translation (state : State D) :
    Q D H (LatticeBcGhostTensorStateField.translation D state) =
      LatticeBcGhostTensorStateField.translation D (Q D H state) := by
  rw [LatticeBcGhostTensorJacobi.stateField_translation_as_mode,
    LatticeBcGhostBrstStateField.Q_derivation_mixed,
    show Q D H (LatticeBcGhostTensorStateField.vacuum D) = 0 from
      LatticeBcGhostBrstCurrent.Q_vacuum D H]
  simp only [map_zero, sub_zero, add_zero]
  exact (LatticeBcGhostTensorJacobi.stateField_translation_as_mode D (Q D H state)).symm

def cycleTranslation : Module.End ℂ (OriginalCycles D H) :=
  ((LatticeBcGhostTensorStateField.translation D).comp (OriginalCycles D H).subtype).codRestrict
    (OriginalCycles D H) (fun state => by
      change Q D H (LatticeBcGhostTensorStateField.translation D state.val) = 0
      rw [Q_translation, show Q D H state.val = 0 from state.property, map_zero])

theorem cycleTranslation_boundary (state : OriginalCycles D H)
    (boundary : state ∈ OriginalBoundaries D H) :
    cycleTranslation D H state ∈ OriginalBoundaries D H := by
  obtain ⟨preimage, equality⟩ := boundary
  refine ⟨LatticeBcGhostTensorStateField.translation D preimage, ?_⟩
  change Q D H (LatticeBcGhostTensorStateField.translation D preimage) =
    LatticeBcGhostTensorStateField.translation D state.val
  rw [Q_translation, equality]
  rfl

def translation : Module.End ℂ (OriginalCohomology D H) :=
  (OriginalBoundaries D H).mapQ (OriginalBoundaries D H) (cycleTranslation D H)
    (cycleTranslation_boundary D H)

theorem translation_mk (state : OriginalCycles D H) :
    translation D H ((OriginalBoundaries D H).mkQ state) =
      (OriginalBoundaries D H).mkQ (cycleTranslation D H state) := rfl

theorem translation_vacuum : translation D H (vacuum D H) = 0 := by
  rw [vacuum, translation_mk]
  have zero : cycleTranslation D H (cycleVacuum D H) = 0 := by
    apply Subtype.ext
    exact LatticeBcGhostTensorStateField.translation_vacuum D
  rw [zero, map_zero]

theorem translation_as_mode (state : OriginalCohomology D H) :
    translation D H state = product D H (-2) state (vacuum D H) := by
  obtain ⟨representative, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective state
  rw [vacuum, product_mk, translation_mk]
  congr 1
  apply Subtype.ext
  exact LatticeBcGhostTensorJacobi.stateField_translation_as_mode D representative.val

theorem covariance (state input : OriginalCohomology D H) (mode : ℤ) :
    translation D H (product D H mode state input) -
      product D H mode state (translation D H input) =
        -(mode : ℂ) • product D H (mode - 1) state input := by
  obtain ⟨representative, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective state
  obtain ⟨vector, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective input
  rw [product_mk, translation_mk, translation_mk, product_mk, product_mk, ← map_sub, ← map_smul]
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun (LatticeBcGhostTensorStateField.stateField_covariance D representative.val mode)
    vector.val

theorem derivative (state input : OriginalCohomology D H) (mode : ℤ) :
    product D H mode (translation D H state) input =
      -(mode : ℂ) • product D H (mode - 1) state input := by
  obtain ⟨representative, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective state
  obtain ⟨vector, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective input
  rw [translation_mk, product_mk, product_mk, ← map_smul]
  congr 1
  apply Subtype.ext
  change ((LatticeBcGhostTensorStateField.stateField D
    (LatticeBcGhostTensorStateField.translation D representative.val))[[mode]]) vector.val = _
  rw [LatticeBcGhostTensorJacobi.stateField_translation, SuperFieldProducts.derivative_modes]
  simp only [SuperFieldProducts.integerBinomial, Nat.cast_one, Ring.choose_one_right,
    show (-mode - 1 + 1 : ℤ) = -mode by omega, Int.cast_neg,
    LinearMap.smul_apply, Submodule.coe_smul]
  all_goals rfl

#print axioms stateField
#print axioms Q_translation
#print axioms covariance
#print axioms derivative

end D5.S3.VertexAlgebra.LatticeBcGhostCohomologyFields
