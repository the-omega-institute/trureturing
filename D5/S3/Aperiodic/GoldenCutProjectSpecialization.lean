/- GID: D5/S3/Aperiodic/GoldenCutProjectSpecialization
   generality: I
   mirror-B: D5/B/S3/Aperiodic/GoldenCutProjectSpecialization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The existing golden lattice-window set is an accepted model set for generic physical and internal projections. -/

import D5.S3.Aperiodic.AcceptedModelSet
import D5.S1.Deficit.ModelSet.GoldenCutAndProject
import Mathlib.Tactic

/-!
# Golden cut-and-project specialization

The existing golden construction lives in the Minkowski plane.  This module
packages the two coordinate projections as generic cut-and-project data and
shows that the existing golden lattice-window set is exactly an accepted model
set whose acceptance predicate is membership in the golden lattice.

The previously frozen inclusion of the canonical natural-number golden model
set is then transported to this generic interface.  The known failure of the
reverse inclusion is preserved: the unrestricted golden lattice-window set
contains lattice points outside the canonical natural-number digit sector.

No new density, regularity, diffraction, or equality with the canonical digit
language is asserted.
-/

/- Library-search audit trail (2026-09-01):
   * `GoldenCutAndProject` owns the golden lattice-window set and the proved
     inclusion from the canonical natural-number golden model set.
   * `AcceptedModelSet` owns the reusable distinction between unrestricted
     window selection and an additional lattice acceptance predicate.
   * This file only instantiates those owners and proves definitional
     compatibility; it does not duplicate the golden window or lattice. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Aperiodic.GoldenCutProjectSpecialization

open D5.S3.Aperiodic.AlgebraicCutProjectData
open D5.S3.Aperiodic.AcceptedModelSet
open D5.S1.Deficit.ModelSet.GoldenCutAndProject
open D5.S1.Deficit.GoldenModelSetSelfSimilar
open D5.S1.Scale

/-- The two coordinate projections of the Minkowski plane as additive
cut-and-project data. -/
def goldenAmbientCutProjectData : CutProjectData (ℝ × ℝ) ℝ ℝ where
  physicalProjection :=
    { toFun := Prod.fst
      map_zero' := rfl
      map_add' := by intro left right; rfl }
  internalProjection :=
    { toFun := Prod.snd
      map_zero' := rfl
      map_add' := by intro left right; rfl }

/-- Acceptance predicate selecting the existing golden lattice inside its
ambient Minkowski plane. -/
def IsGoldenLatticePoint (point : ℝ × ℝ) : Prop :=
  point ∈ (goldenLattice : Set (ℝ × ℝ))

/-- The generic accepted-model-set construction recovers the existing golden
cut-and-project set exactly. -/
theorem golden_accepted_model_set_eq_existing :
    acceptedModelSet goldenAmbientCutProjectData goldenWindow
        IsGoldenLatticePoint =
      goldenCutAndProjectSet := by
  ext physicalPoint
  constructor
  · rintro ⟨point, hLattice, hPhysical, hInternal⟩
    exact ⟨point, hLattice, hPhysical, hInternal⟩
  · rintro ⟨point, hLattice, hPhysical, hInternal⟩
    exact ⟨point, hLattice, hPhysical, hInternal⟩

/-- The canonical natural-number golden model set lies in the generic accepted
model set. -/
theorem golden_model_set_subset_generic_accepted :
    embedding '' goldenModelSet ⊆
      acceptedModelSet goldenAmbientCutProjectData goldenWindow
        IsGoldenLatticePoint := by
  rw [golden_accepted_model_set_eq_existing]
  exact golden_model_set_subset_cut_and_project

/-- Dropping golden-lattice acceptance enlarges the construction to the full
ambient-plane window model set. -/
theorem golden_accepted_subset_unrestricted :
    acceptedModelSet goldenAmbientCutProjectData goldenWindow
        IsGoldenLatticePoint ⊆
      modelSet goldenAmbientCutProjectData goldenWindow := by
  exact acceptedModelSet_subset_modelSet _ _ _

/-- The generic physical projection is the existing first-coordinate
projection. -/
theorem golden_physical_projection_eq
    (point : ℝ × ℝ) :
    goldenAmbientCutProjectData.physicalProjection point =
      physicalProjection point := by
  rfl

/-- The generic internal projection is the existing conjugate-coordinate
projection. -/
theorem golden_internal_projection_eq
    (point : ℝ × ℝ) :
    goldenAmbientCutProjectData.internalProjection point =
      internalProjection point := by
  rfl

example :
    embedding (betaGolden 0) ∈
      acceptedModelSet goldenAmbientCutProjectData goldenWindow
        IsGoldenLatticePoint := by
  apply golden_model_set_subset_generic_accepted
  exact ⟨betaGolden 0, ⟨0, rfl⟩, rfl⟩

#print axioms golden_accepted_model_set_eq_existing
#print axioms golden_model_set_subset_generic_accepted
#print axioms golden_accepted_subset_unrestricted
#print axioms golden_physical_projection_eq
#print axioms golden_internal_projection_eq

end D5.S3.Aperiodic.GoldenCutProjectSpecialization
