/- GID: D5/S3/VertexAlgebra/LatticeBcGhostCohomologySuperVertex
   generality: I
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed state-field interface and genuine critical original BRST cohomology instance. -/

import D5.S3.VertexAlgebra.LatticeBcGhostCohomologyParity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeBcGhostCohomologySuperVertex

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeBcGhostBrstCharge (State Q)
open LatticeBcGhostNeutralCohomology (OriginalCycles OriginalCohomology original_image_in_cycles)
open SuperFieldProducts
open scoped VertexOperator

theorem actual_stateField_mode (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (state : OriginalCohomology D H) (mode : ℤ) :
    ((LatticeBcGhostCohomologyFields.stateField D H state)[[mode]]) =
      LatticeBcGhostCohomologyModes.product D H mode state := by
  change ((LatticeBcGhostCohomologyFields.field D H state)[[mode]]) = _
  exact LatticeBcGhostCohomologyFields.field_mode D H state mode

structure SignedStateFieldVertexAlgebra (Space : Type*) [AddCommGroup Space] [Module ℂ Space] where
  parity : ℕ → Module.End ℂ Space
  parity_periodic : ∀ (first second : ℕ), first % 2 = second % 2 →
    ∀ state, parity first state = parity second state
  parity_idempotent : ∀ grade state, parity grade (parity grade state) = parity grade state
  parity_orthogonal : ∀ (first second : ℕ), first % 2 ≠ second % 2 →
    ∀ state, parity first (parity second state) = 0
  parity_decomposition : ∀ state, parity 0 state + parity 1 state = state
  stateField : Space →ₗ[ℂ] VertexOperator ℂ Space
  lower_truncation : ∀ state input, ∃ bound : ℤ, ∀ mode : ℤ,
    bound < mode → ((stateField state)[[mode]]) input = 0
  vacuum : Space
  translation : Module.End ℂ Space
  vacuum_even : parity 0 vacuum = vacuum
  mode_parity : ∀ (leftGrade rightGrade : ℕ) (left right : Space),
    parity leftGrade left = left → parity rightGrade right = right → ∀ mode : ℤ,
      parity (leftGrade + rightGrade) (((stateField left)[[mode]]) right) =
        ((stateField left)[[mode]]) right
  vacuum_modes : ∀ (state : Space) (mode : ℤ),
    ((stateField vacuum)[[mode]]) state = if mode = -1 then state else 0
  creation : ∀ state, ((stateField state)[[-1]]) vacuum = state
  creativity : ∀ (state : Space) (mode : ℤ),
    0 ≤ mode → ((stateField state)[[mode]]) vacuum = 0
  translation_vacuum : translation vacuum = 0
  translation_parity : ∀ grade state, parity grade state = state →
    parity grade (translation state) = translation state
  covariance : ∀ (state input : Space) (mode : ℤ),
    translation (((stateField state)[[mode]]) input) -
      ((stateField state)[[mode]]) (translation input) =
        -(mode : ℂ) • ((stateField state)[[mode - 1]]) input
  derivative : ∀ (state input : Space) (mode : ℤ),
    ((stateField (translation state))[[mode]]) input =
      -(mode : ℂ) • ((stateField state)[[mode - 1]]) input
  locality : ∀ (leftGrade rightGrade : ℕ) (left right : Space),
    parity leftGrade left = left → parity rightGrade right = right →
      SuperLocal leftGrade rightGrade (stateField left) (stateField right)
  borcherds : ∀ (leftGrade rightGrade : ℕ) (first parameter last : ℤ)
    (left right input : Space),
    parity leftGrade left = left → parity rightGrade right = right →
    let mode : Space → ℤ → Space → Space := fun state index vector =>
      ((stateField state)[[index]]) vector
    let leftTerm : ℕ → Space := fun offset => integerBinomial first offset •
      mode (mode left (parameter + offset) right) (first + last - offset) input
    let rightTerm : ℕ → Space := fun offset => weight parameter offset •
      (mode left (first + parameter - offset) (mode right (last + offset) input) -
        (epsilon parameter * koszul leftGrade rightGrade) •
          mode right (parameter + last - offset) (mode left (first + offset) input))
    Function.HasFiniteSupport leftTerm ∧ Function.HasFiniteSupport rightTerm ∧
      (∑ᶠ offset : ℕ, leftTerm offset) = ∑ᶠ offset : ℕ, rightTerm offset

def actualSuperVertex (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    SignedStateFieldVertexAlgebra (OriginalCohomology D H) where
  parity := LatticeBcGhostCohomologyModes.parity D H
  parity_periodic := LatticeBcGhostCohomologyParity.parity_periodic D H
  parity_idempotent := LatticeBcGhostCohomologyParity.parity_idempotent D H
  parity_orthogonal := LatticeBcGhostCohomologyParity.parity_orthogonal D H
  parity_decomposition := LatticeBcGhostCohomologyModes.parity_decomposition D H
  stateField := LatticeBcGhostCohomologyFields.stateField D H
  lower_truncation state input := by
    simpa only [actual_stateField_mode] using
      LatticeBcGhostCohomologyModes.product_lower_truncation D H state input
  vacuum := LatticeBcGhostCohomologyFields.vacuum D H
  translation := LatticeBcGhostCohomologyFields.translation D H
  vacuum_even := LatticeBcGhostCohomologyParity.vacuum_even D H
  mode_parity leftGrade rightGrade left right leftFixed rightFixed mode := by
    simpa only [actual_stateField_mode] using
      LatticeBcGhostCohomologyParity.product_parity D H leftGrade rightGrade left right
        leftFixed rightFixed mode
  vacuum_modes state mode := by
    simpa only [actual_stateField_mode] using
      LatticeBcGhostCohomologyFields.vacuum_product D H state mode
  creation state := by
    simpa only [actual_stateField_mode] using
      LatticeBcGhostCohomologyFields.creation D H state
  creativity state mode nonnegative := by
    simpa only [actual_stateField_mode] using
      LatticeBcGhostCohomologyFields.creativity D H state mode nonnegative
  translation_vacuum := LatticeBcGhostCohomologyFields.translation_vacuum D H
  translation_parity := LatticeBcGhostCohomologyParity.translation_parity D H
  covariance state input mode := by
    simpa only [actual_stateField_mode] using
      LatticeBcGhostCohomologyFields.covariance D H state input mode
  derivative state input mode := by
    simpa only [actual_stateField_mode] using
      LatticeBcGhostCohomologyFields.derivative D H state input mode
  locality := LatticeBcGhostCohomologyFields.superLocal D H
  borcherds leftGrade rightGrade first parameter last left right input leftFixed rightFixed := by
    dsimp only
    simp only [actual_stateField_mode]
    change Function.HasFiniteSupport
        (LatticeBcGhostCohomologyJacobi.leftTerm D H first parameter last left right input) ∧
      Function.HasFiniteSupport
        (LatticeBcGhostCohomologyJacobi.rightTerm D H leftGrade rightGrade
          first parameter last left right input) ∧
      LatticeBcGhostCohomologyJacobi.leftSum D H first parameter last left right input =
        LatticeBcGhostCohomologyJacobi.rightSum D H leftGrade rightGrade
          first parameter last left right input
    exact ⟨LatticeBcGhostCohomologyJacobi.leftTerm_finite D H first parameter last left right input,
      LatticeBcGhostCohomologyJacobi.rightTerm_finite D H leftGrade rightGrade
        first parameter last left right input,
      LatticeBcGhostCohomologyJacobi.borcherds D H leftGrade rightGrade first parameter last
        left right input leftFixed rightFixed⟩

structure CriticalOriginalBRSTSuperVertex (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) where
  left_inverse : H * gramComplex D = 1
  right_inverse : gramComplex D * H = 1
  rank26 : D.rank = 26
  image_in_cycles : LinearMap.range (Q D H) ≤ OriginalCycles D H
  square_zero : Q D H * Q D H = 0
  vertex : SignedStateFieldVertexAlgebra (OriginalCohomology D H)

def criticalSuperVertex (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (critical : D.rank = 26) : CriticalOriginalBRSTSuperVertex D H where
  left_inverse := hHG
  right_inverse := hGH
  rank26 := critical
  image_in_cycles := original_image_in_cycles D H hHG hGH critical
  square_zero := LatticeBcGhostBrstNilpotence.nilpotent D H hHG hGH critical
  vertex := actualSuperVertex D H

#print axioms actualSuperVertex
#print axioms criticalSuperVertex

end D5.S3.VertexAlgebra.LatticeBcGhostCohomologySuperVertex
