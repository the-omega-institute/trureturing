/- GID: D5/S3/VertexAlgebra/LatticeBcGhostCohomologyJacobi
   generality: I
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All integer signed coefficient Jacobi identities descend to the actual original BRST quotient. -/

import D5.S3.VertexAlgebra.LatticeBcGhostCohomologyModes

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeBcGhostCohomologyJacobi

open LatticeGeneratingFieldLocality
open LatticeBcGhostNeutralCohomology (OriginalCycles OriginalBoundaries OriginalCohomology)
open LatticeBcGhostCohomologyModes
open SuperFieldProducts

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

def cycleLeftTerm (first parameter last : ℤ) (left right vector : OriginalCycles D H)
    (offset : ℕ) : OriginalCycles D H :=
  integerBinomial first offset • cycleMode D H (first + last - offset)
    (cycleMode D H (parameter + offset) left right) vector

def cycleRightTerm (leftParity rightParity : ℕ) (first parameter last : ℤ)
    (left right vector : OriginalCycles D H) (offset : ℕ) : OriginalCycles D H :=
  weight parameter offset •
    (cycleMode D H (first + parameter - offset) left
      (cycleMode D H (last + offset) right vector) -
    (epsilon parameter * koszul leftParity rightParity) •
      cycleMode D H (parameter + last - offset) right
        (cycleMode D H (first + offset) left vector))

theorem cycleLeftTerm_val (first parameter last : ℤ) (left right vector : OriginalCycles D H)
    (offset : ℕ) :
    (cycleLeftTerm D H first parameter last left right vector offset).val =
      LatticeBcGhostTensorJacobi.borcherdsLeftTerm D first parameter last
        left.val right.val vector.val offset := rfl

theorem cycleRightTerm_val (leftParity rightParity : ℕ) (first parameter last : ℤ)
    (left right vector : OriginalCycles D H) (offset : ℕ) :
    (cycleRightTerm D H leftParity rightParity first parameter last left right vector offset).val =
      LatticeBcGhostTensorJacobi.borcherdsRightTerm leftParity rightParity D first parameter last
        left.val right.val vector.val offset := rfl

theorem cycleLeftTerm_finite (first parameter last : ℤ) (left right vector : OriginalCycles D H) :
    Function.HasFiniteSupport (cycleLeftTerm D H first parameter last left right vector) := by
  apply (LatticeBcGhostTensorJacobi.borcherds_left_finite D first parameter last
    left.val right.val vector.val).subset
  intro offset nonzero zero
  apply nonzero
  apply Subtype.ext
  exact zero

theorem cycleRightTerm_finite (leftParity rightParity : ℕ) (first parameter last : ℤ)
    (left right vector : OriginalCycles D H) :
    Function.HasFiniteSupport
      (cycleRightTerm D H leftParity rightParity first parameter last left right vector) := by
  apply (LatticeBcGhostTensorJacobi.borcherds_right_finite leftParity rightParity D
    first parameter last left.val right.val vector.val).subset
  intro offset nonzero zero
  apply nonzero
  apply Subtype.ext
  exact zero

def cycleLeft (first parameter last : ℤ) (left right vector : OriginalCycles D H) :
    OriginalCycles D H := ∑ᶠ offset : ℕ, cycleLeftTerm D H first parameter last left right vector offset

def cycleRight (leftParity rightParity : ℕ) (first parameter last : ℤ)
    (left right vector : OriginalCycles D H) : OriginalCycles D H :=
  ∑ᶠ offset : ℕ, cycleRightTerm D H leftParity rightParity first parameter last left right vector offset

theorem cycleLeft_val (first parameter last : ℤ) (left right vector : OriginalCycles D H) :
    (cycleLeft D H first parameter last left right vector).val =
      LatticeBcGhostTensorJacobi.borcherdsLeft D first parameter last left.val right.val vector.val := by
  exact (OriginalCycles D H).subtype.toAddMonoidHom.map_finsum_of_injective
    Subtype.val_injective (cycleLeftTerm D H first parameter last left right vector)

theorem cycleRight_val (leftParity rightParity : ℕ) (first parameter last : ℤ)
    (left right vector : OriginalCycles D H) :
    (cycleRight D H leftParity rightParity first parameter last left right vector).val =
      LatticeBcGhostTensorJacobi.borcherdsRight leftParity rightParity D first parameter last
        left.val right.val vector.val := by
  exact (OriginalCycles D H).subtype.toAddMonoidHom.map_finsum_of_injective
    Subtype.val_injective (cycleRightTerm D H leftParity rightParity first parameter last left right vector)

def leftTerm (first parameter last : ℤ) (left right vector : OriginalCohomology D H)
    (offset : ℕ) : OriginalCohomology D H :=
  integerBinomial first offset • product D H (first + last - offset)
    (product D H (parameter + offset) left right) vector

def rightTerm (leftParity rightParity : ℕ) (first parameter last : ℤ)
    (left right vector : OriginalCohomology D H) (offset : ℕ) : OriginalCohomology D H :=
  weight parameter offset •
    (product D H (first + parameter - offset) left
      (product D H (last + offset) right vector) -
    (epsilon parameter * koszul leftParity rightParity) •
      product D H (parameter + last - offset) right
        (product D H (first + offset) left vector))

theorem leftTerm_mk (first parameter last : ℤ) (left right vector : OriginalCycles D H)
    (offset : ℕ) :
    leftTerm D H first parameter last ((OriginalBoundaries D H).mkQ left)
      ((OriginalBoundaries D H).mkQ right) ((OriginalBoundaries D H).mkQ vector) offset =
        (OriginalBoundaries D H).mkQ (cycleLeftTerm D H first parameter last left right vector offset) := by
  simp only [leftTerm, cycleLeftTerm, product_mk, map_smul]

theorem rightTerm_mk (leftParity rightParity : ℕ) (first parameter last : ℤ)
    (left right vector : OriginalCycles D H) (offset : ℕ) :
    rightTerm D H leftParity rightParity first parameter last ((OriginalBoundaries D H).mkQ left)
      ((OriginalBoundaries D H).mkQ right) ((OriginalBoundaries D H).mkQ vector) offset =
        (OriginalBoundaries D H).mkQ
          (cycleRightTerm D H leftParity rightParity first parameter last left right vector offset) := by
  simp only [rightTerm, cycleRightTerm, product_mk, map_smul, map_sub]

def leftSum (first parameter last : ℤ) (left right vector : OriginalCohomology D H) :
    OriginalCohomology D H := ∑ᶠ offset : ℕ, leftTerm D H first parameter last left right vector offset

def rightSum (leftParity rightParity : ℕ) (first parameter last : ℤ)
    (left right vector : OriginalCohomology D H) : OriginalCohomology D H :=
  ∑ᶠ offset : ℕ, rightTerm D H leftParity rightParity first parameter last left right vector offset

theorem leftSum_mk (first parameter last : ℤ) (left right vector : OriginalCycles D H) :
    leftSum D H first parameter last ((OriginalBoundaries D H).mkQ left)
      ((OriginalBoundaries D H).mkQ right) ((OriginalBoundaries D H).mkQ vector) =
        (OriginalBoundaries D H).mkQ (cycleLeft D H first parameter last left right vector) := by
  simp only [leftSum, leftTerm_mk]
  exact ((OriginalBoundaries D H).mkQ.toAddMonoidHom.map_finsum
    (cycleLeftTerm_finite D H first parameter last left right vector)).symm

theorem rightSum_mk (leftParity rightParity : ℕ) (first parameter last : ℤ)
    (left right vector : OriginalCycles D H) :
    rightSum D H leftParity rightParity first parameter last ((OriginalBoundaries D H).mkQ left)
      ((OriginalBoundaries D H).mkQ right) ((OriginalBoundaries D H).mkQ vector) =
        (OriginalBoundaries D H).mkQ
          (cycleRight D H leftParity rightParity first parameter last left right vector) := by
  simp only [rightSum, rightTerm_mk]
  exact ((OriginalBoundaries D H).mkQ.toAddMonoidHom.map_finsum
    (cycleRightTerm_finite D H leftParity rightParity first parameter last left right vector)).symm

theorem leftTerm_finite (first parameter last : ℤ) (left right vector : OriginalCohomology D H) :
    Function.HasFiniteSupport (leftTerm D H first parameter last left right vector) := by
  obtain ⟨firstState, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective left
  obtain ⟨secondState, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective right
  obtain ⟨input, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective vector
  apply (cycleLeftTerm_finite D H first parameter last firstState secondState input).subset
  intro offset nonzero zero
  apply nonzero
  rw [leftTerm_mk, zero, map_zero]

theorem rightTerm_finite (leftParity rightParity : ℕ) (first parameter last : ℤ)
    (left right vector : OriginalCohomology D H) :
    Function.HasFiniteSupport (rightTerm D H leftParity rightParity first parameter last left right vector) := by
  obtain ⟨firstState, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective left
  obtain ⟨secondState, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective right
  obtain ⟨input, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective vector
  apply (cycleRightTerm_finite D H leftParity rightParity first parameter last firstState secondState input).subset
  intro offset nonzero zero
  apply nonzero
  rw [rightTerm_mk, zero, map_zero]

theorem projected_borcherds (leftParity rightParity : ℕ) (first parameter last : ℤ)
    (left right vector : OriginalCycles D H) :
    leftSum D H first parameter last
      ((OriginalBoundaries D H).mkQ (cycleParity D H leftParity left))
      ((OriginalBoundaries D H).mkQ (cycleParity D H rightParity right))
      ((OriginalBoundaries D H).mkQ vector) =
    rightSum D H leftParity rightParity first parameter last
      ((OriginalBoundaries D H).mkQ (cycleParity D H leftParity left))
      ((OriginalBoundaries D H).mkQ (cycleParity D H rightParity right))
      ((OriginalBoundaries D H).mkQ vector) := by
  rw [leftSum_mk, rightSum_mk]
  congr 1
  apply Subtype.ext
  rw [cycleLeft_val, cycleRight_val]
  exact LatticeBcGhostTensorJacobi.borcherds D leftParity rightParity _ _ vector.val
    (LatticeBcGhostTensorStateField.parityPart_mem leftParity left.val)
    (LatticeBcGhostTensorStateField.parityPart_mem rightParity right.val) first last parameter

theorem borcherds (leftParity rightParity : ℕ) (first parameter last : ℤ)
    (left right vector : OriginalCohomology D H)
    (leftFixed : parity D H leftParity left = left)
    (rightFixed : parity D H rightParity right = right) :
    leftSum D H first parameter last left right vector =
      rightSum D H leftParity rightParity first parameter last left right vector := by
  obtain ⟨firstState, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective left
  obtain ⟨secondState, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective right
  obtain ⟨input, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective vector
  rw [← leftFixed, ← rightFixed, parity_mk, parity_mk]
  exact projected_borcherds D H leftParity rightParity first parameter last firstState secondState input

theorem mixed_borcherds (first parameter last : ℤ) (left right vector : OriginalCohomology D H) :
    leftSum D H first parameter last left right vector =
      (rightSum D H 0 0 first parameter last (parity D H 0 left) (parity D H 0 right) vector +
        rightSum D H 0 1 first parameter last (parity D H 0 left) (parity D H 1 right) vector) +
      (rightSum D H 1 0 first parameter last (parity D H 1 left) (parity D H 0 right) vector +
        rightSum D H 1 1 first parameter last (parity D H 1 left) (parity D H 1 right) vector) := by
  obtain ⟨firstState, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective left
  obtain ⟨secondState, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective right
  obtain ⟨input, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective vector
  simp only [parity_mk, leftSum_mk, rightSum_mk, ← map_add]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_add, cycleLeft_val, cycleRight_val]
  exact LatticeBcGhostTensorJacobi.mixed_borcherds D first parameter last
    firstState.val secondState.val input.val

#print axioms borcherds
#print axioms mixed_borcherds

end D5.S3.VertexAlgebra.LatticeBcGhostCohomologyJacobi
