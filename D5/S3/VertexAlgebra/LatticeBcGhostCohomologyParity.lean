/- GID: D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity
   generality: I
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual parity projections and homogeneous modes on the full original BRST quotient. -/

import D5.S3.VertexAlgebra.LatticeBcGhostCohomologyLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeBcGhostCohomologyParity

open LatticeGeneratingFieldLocality
open LatticeBcGhostNeutralCohomology (OriginalCycles OriginalBoundaries OriginalCohomology)
open LatticeBcGhostCohomologyModes
open LatticeBcGhostCohomologyFields (cycleVacuum vacuum cycleTranslation translation translation_mk)
open scoped VertexOperator

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

theorem parity_idempotent (grade : ℕ) (state : OriginalCohomology D H) :
    parity D H grade (parity D H grade state) = parity D H grade state := by
  obtain ⟨representative, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective state
  rw [parity_mk, parity_mk]
  congr 1
  apply Subtype.ext
  exact LatticeBcGhostTensorStateField.parityPart_idempotent grade representative.val

theorem parity_orthogonal (first second : ℕ) (different : first % 2 ≠ second % 2)
    (state : OriginalCohomology D H) :
    parity D H first (parity D H second state) = 0 := by
  obtain ⟨representative, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective state
  rw [parity_mk, parity_mk]
  have zero : cycleParity D H first (cycleParity D H second representative) = 0 := by
    apply Subtype.ext
    exact LatticeBcGhostTensorStateField.parityPart_orthogonal first second different
      representative.val
  rw [zero, map_zero]

theorem parity_periodic (first second : ℕ) (same : first % 2 = second % 2)
    (state : OriginalCohomology D H) : parity D H first state = parity D H second state := by
  obtain ⟨representative, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective state
  rw [parity_mk, parity_mk]
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun (parityPart_periodic D first second same) representative.val

theorem homogeneous_representative (grade : ℕ) (state : OriginalCohomology D H)
    (fixed : parity D H grade state = state) :
    ∃ representative : OriginalCycles D H,
      (OriginalBoundaries D H).mkQ representative = state ∧
        representative.val ∈ LatticeBcGhostTensorStateField.homogeneous grade := by
  obtain ⟨representative, equality⟩ := (OriginalBoundaries D H).mkQ_surjective state
  refine ⟨cycleParity D H grade representative, ?_, ?_⟩
  · rw [← parity_mk, equality, fixed]
  · exact LatticeBcGhostTensorStateField.parityPart_mem grade representative.val

theorem product_parity (leftGrade rightGrade : ℕ) (left right : OriginalCohomology D H)
    (leftFixed : parity D H leftGrade left = left)
    (rightFixed : parity D H rightGrade right = right) (mode : ℤ) :
    parity D H (leftGrade + rightGrade) (product D H mode left right) =
      product D H mode left right := by
  obtain ⟨first, rfl, firstMember⟩ := homogeneous_representative D H leftGrade left leftFixed
  obtain ⟨second, rfl, secondMember⟩ := homogeneous_representative D H rightGrade right rightFixed
  rw [product_mk, parity_mk]
  congr 1
  apply Subtype.ext
  exact (LatticeBcGhostTensorStateField.homogeneous_fixed (leftGrade + rightGrade) _).mp
    (LatticeBcGhostTensorStateField.stateField_mem (D := D) leftGrade rightGrade
      first.val second.val firstMember secondMember mode)

theorem vacuum_even : parity D H 0 (vacuum D H) = vacuum D H := by
  rw [vacuum, parity_mk]
  congr 1
  apply Subtype.ext
  change LatticeBcGhostTensorStateField.parityPart 0
      (LatticeBcGhostTensorStateField.vacuum D) = LatticeBcGhostTensorStateField.vacuum D
  apply (LatticeBcGhostTensorStateField.homogeneous_fixed 0 _).mp
  apply LatticeBcGhostTensorStateField.tmul_mem
  exact BcGhostSuperGenerators.single_mem 0 ∅ 1 (by simp [BcGhostSuperGenerators.subsetParity])

theorem translation_parity (grade : ℕ) (state : OriginalCohomology D H)
    (fixed : parity D H grade state = state) :
    parity D H grade (translation D H state) = translation D H state := by
  obtain ⟨representative, rfl, member⟩ := homogeneous_representative D H grade state fixed
  rw [translation_mk, parity_mk]
  congr 1
  apply Subtype.ext
  exact (LatticeBcGhostTensorStateField.homogeneous_fixed grade _).mp
    (LatticeBcGhostTensorJacobi.translation_mem D grade representative.val member)

#print axioms homogeneous_representative
#print axioms product_parity
#print axioms parity_idempotent
#print axioms parity_orthogonal
#print axioms vacuum_even
#print axioms translation_parity

end D5.S3.VertexAlgebra.LatticeBcGhostCohomologyParity
