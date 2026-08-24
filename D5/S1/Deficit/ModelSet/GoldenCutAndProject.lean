/- GID: D5/S1/Deficit/ModelSet/GoldenCutAndProject
   generality: I
   mirror-B: D5/B/S1/Deficit/ModelSet/GoldenCutAndProject
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The physical golden beta range lies in the golden-lattice cut-and-project set; the reverse inclusion is not covered. -/

import D5.S1.Deficit.ModelSet.GoldenModelSetSelfSimilar
import D5.S1.Scale.MinkowskiModelSet
import D5.S1.Words.Expansions.BasePhiNegativeBridge

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'golden_model_set_subset_cut_and_project' D5 Golden/Frozen/accepted`
     returned no matches.
   * Searches for `cutAndProject`, `model set`, `window`, and `betaContraction` found
     `MinkowskiModelSet.goldenLattice`, `MinkowskiModelSet.modelSet`, and the public
     `BasePhiNegativeBridge.betaContraction_mem_window`, but no identification of the
     natural-number beta range with a cut-and-project set.
   * `GoldenModelSetSelfSimilar.goldenModelSet` and `.goldenWindow` are reused, as are
     `Scale.minkowskiEmbedding`, `Scale.goldenLattice`, and the public window bound.
   * `DeficitThreeValued` contains private window-bound machinery; private declarations
     are not treated as coverage. The proof below uses the public bound, the lattice-range
     definition, coordinate projections, and standard golden-ratio identities.
   * The reverse inclusion is false for the unrestricted lattice with the current
     natural-number beta range: `-phi` lies over the right window endpoint but has
     negative `b`-coordinate. Accordingly this module proves only the requested fallback.
   -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Deficit.ModelSet.GoldenCutAndProject

open D5.S0.Carrier
open D5.S0.Conventions
open D5.S1.Deficit
open D5.S1.Deficit.GoldenModelSetSelfSimilar
open D5.S1.Scale
open D5.S1.Words.Expansions.BasePhiNegativeBridge

/-- Projection from Minkowski space to the physical coordinate. -/
def physicalProjection (point : ℝ × ℝ) : ℝ := point.1

/-- Projection from Minkowski space to the internal Galois-conjugate coordinate. -/
def internalProjection (point : ℝ × ℝ) : ℝ := point.2

/-- Physical projections of golden lattice points whose internal coordinate is in the window. -/
noncomputable def goldenCutAndProjectSet : Set ℝ :=
  {y | ∃ point ∈ (goldenLattice : Set (ℝ × ℝ)),
    physicalProjection point = y ∧ internalProjection point ∈ goldenWindow}

/-- Every physical value represented by a canonical natural-number golden expansion is selected
by the golden lattice and the closed conjugate window. -/
theorem golden_model_set_subset_cut_and_project :
    embedding '' goldenModelSet ⊆ goldenCutAndProjectSet := by
  rintro y ⟨x, ⟨v, rfl⟩, rfl⟩
  refine ⟨minkowskiEmbedding (betaGolden v), ⟨betaGolden v, rfl⟩, rfl, ?_⟩
  change betaContraction v ∈ goldenWindow
  rw [goldenWindow, Set.mem_Icc, Real.inv_goldenRatio]
  simpa using betaContraction_mem_window v

example : embedding (betaGolden 0) ∈ goldenCutAndProjectSet := by
  apply golden_model_set_subset_cut_and_project
  exact ⟨betaGolden 0, ⟨0, rfl⟩, rfl⟩

#print axioms golden_model_set_subset_cut_and_project

end D5.S1.Deficit.ModelSet.GoldenCutAndProject
