/- GID: D5/S3/Aperiodic/GoldenCutProjectSpecialization
   generality: I
   mirror-B: D5/B/S3/Aperiodic/GoldenCutProjectSpecialization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The frozen golden lattice and window instantiate the generic cut-and-project interface, while natural beta expansions form an accepted sector. -/

import D5.S3.Aperiodic.AcceptedModelSet
import D5.S1.Deficit.ModelSet.GoldenCutAndProject
import Mathlib.Tactic

/-!
# Golden cut-and-project specialization

The existing golden Minkowski lattice, physical coordinate, conjugate
coordinate, and golden window instantiate the generic set-level
cut-and-project datum. Its generic model set is definitionally the previously
frozen golden cut-and-project set.

Natural-number beta expansions impose an additional admissibility sector on
lattice witnesses. The resulting accepted model set is exactly the physical
image of the frozen natural golden model set. This explains why the earlier
full reverse inclusion failed: the geometric window permits lattice points
outside the natural digit-language sector.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Aperiodic.GoldenCutProjectSpecialization

open D5.S0.Carrier
open D5.S1.Deficit
open D5.S1.Deficit.GoldenModelSetSelfSimilar
open D5.S1.Deficit.ModelSet.GoldenCutAndProject
open D5.S1.Scale
open D5.S1.Words.Expansions.BasePhiNegativeBridge
open D5.S3.Aperiodic.AlgebraicCutProjectData
open D5.S3.Aperiodic.AcceptedModelSet

/-- Generic cut-and-project datum carried by the frozen golden Minkowski
lattice. -/
noncomputable def goldenCutProjectData :
    CutProjectData (ℝ × ℝ) ℝ ℝ where
  lattice := (goldenLattice : Set (ℝ × ℝ))
  physicalProjection := Prod.fst
  internalProjection := Prod.snd

/-- The generic model-set construction recovers the existing golden
cut-and-project set exactly. -/
theorem goldenCutProject_modelSet_eq :
    goldenCutProjectData.modelSet goldenWindow =
      goldenCutAndProjectSet := by
  ext point
  rfl

/-- Existing natural golden values therefore lie in the generic model set. -/
theorem golden_model_set_subset_generic_cut_project :
    embedding '' goldenModelSet ⊆
      goldenCutProjectData.modelSet goldenWindow := by
  rw [goldenCutProject_modelSet_eq]
  exact golden_model_set_subset_cut_and_project

/-- Lattice points arising from natural-number beta expansions. -/
def IsNaturalGoldenWitness (point : ℝ × ℝ) : Prop :=
  ∃ value : ℕ, minkowskiEmbedding (betaGolden value) = point

/-- The accepted golden model set selected by the natural beta-language
sector. -/
noncomputable def acceptedNaturalGoldenModelSet : Set ℝ :=
  acceptedModelSet goldenCutProjectData goldenWindow
    IsNaturalGoldenWitness

/-- Natural beta expansions supply accepted cut-and-project witnesses. -/
theorem golden_model_set_subset_accepted :
    embedding '' goldenModelSet ⊆ acceptedNaturalGoldenModelSet := by
  rintro point ⟨value, ⟨natural, rfl⟩, rfl⟩
  refine ⟨minkowskiEmbedding (betaGolden natural),
    ⟨betaGolden natural, rfl⟩, ⟨natural, rfl⟩, rfl, ?_⟩
  change betaContraction natural ∈ goldenWindow
  rw [goldenWindow, Set.mem_Icc, Real.inv_goldenRatio]
  simpa using betaContraction_mem_window natural

/-- Every accepted witness comes from the natural golden model set. -/
theorem accepted_subset_golden_model_set :
    acceptedNaturalGoldenModelSet ⊆ embedding '' goldenModelSet := by
  rintro point ⟨latticePoint, _hLattice,
    ⟨natural, hNatural⟩, hPhysical, _hInternal⟩
  subst latticePoint
  refine ⟨betaGolden natural, ⟨natural, rfl⟩, ?_⟩
  exact hPhysical

/-- The symbolic natural sector is exactly an accepted model set inside the
full geometric golden cut-and-project set. -/
theorem acceptedNaturalGoldenModelSet_eq :
    acceptedNaturalGoldenModelSet = embedding '' goldenModelSet := by
  exact Set.Subset.antisymm accepted_subset_golden_model_set
    golden_model_set_subset_accepted

/-- The accepted natural sector is contained in the full geometric model set. -/
theorem acceptedNaturalGoldenModelSet_subset_full :
    acceptedNaturalGoldenModelSet ⊆
      goldenCutProjectData.modelSet goldenWindow := by
  exact acceptedModelSet_subset_modelSet _ _ _

example : embedding (betaGolden 0) ∈ acceptedNaturalGoldenModelSet := by
  apply golden_model_set_subset_accepted
  exact ⟨betaGolden 0, ⟨0, rfl⟩, rfl⟩

#print axioms goldenCutProject_modelSet_eq
#print axioms golden_model_set_subset_generic_cut_project
#print axioms golden_model_set_subset_accepted
#print axioms accepted_subset_golden_model_set
#print axioms acceptedNaturalGoldenModelSet_eq

end D5.S3.Aperiodic.GoldenCutProjectSpecialization
