/- GID: D5/S3/ConceptDynamics/Experiments/ExperimentRefinementGainMonotone
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiments/ExperimentRefinementGainMonotone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Refining an experiment can only enlarge the set of repaired target defects. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Order.BooleanAlgebra.Set

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'experiment_refinement_gain_monotone' D5 Golden/Frozen/accepted`
     found no repository declaration or accepted duplicate.
   * `rg -n 'gain|Gain' D5/ --glob '*.lean'` found unrelated lexical hits,
     including entropy's `refinementGain`, but no experiment-defect gain declaration.
   * Repository search found the canonical `Concept`, `Refines`, and `conceptJoin`
     declarations in `ConceptJoinUniversal`; this module imports and reuses them.
   * Mathlib search found `sdiff_subset_sdiff_right`; its deprecated alias is
     `Set.diff_subset_diff_right`. The main proof uses the current set-difference lemma. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Experiments.ExperimentRefinementGainMonotone

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- Target-relevant state pairs that a readout still identifies. -/
def targetDefects {X C Target : Type _} (q_C : Concept X C) (target : X → Target) :
    Set (X × X) :=
  {pair | q_C pair.1 = q_C pair.2 ∧ target pair.1 ≠ target pair.2}

/-- Defects of the current concept that disappear after adjoining an experiment. -/
def experimentGain {X C E Target : Type _} (q_C : Concept X C) (q_E : Concept X E)
    (target : X → Target) : Set (X × X) :=
  targetDefects q_C target \ targetDefects (conceptJoin q_C q_E) target

/-- Target defects are antitone when the readout is refined. -/
lemma targetDefects_antitone_of_refines
    {X D D' Target : Type _} (q_D : Concept X D) (q_D' : Concept X D')
    (target : X → Target) (refinement : Refines q_D q_D') :
    targetDefects q_D' target ⊆ targetDefects q_D target := by
  rintro pair ⟨sameReadout, targetDifferent⟩
  rcases refinement with ⟨factor, factors⟩
  refine ⟨?_, targetDifferent⟩
  rw [factors]
  exact congrArg factor sameReadout

/-- Joining a fixed concept preserves refinement of the experiment component. -/
lemma conceptJoin_refines_of_right_refines
    {X C E E' : Type _} (q_C : Concept X C) (q_E : Concept X E)
    (q_E' : Concept X E') (refinement : Refines q_E q_E') :
    Refines (conceptJoin q_C q_E) (conceptJoin q_C q_E') := by
  rcases refinement with ⟨factor, factors⟩
  refine ⟨fun pair => (pair.1, factor pair.2), ?_⟩
  funext x
  change (q_C x, q_E x) = (q_C x, factor (q_E' x))
  rw [factors]
  rfl

/-- Refining an experiment can only enlarge its gain relative to a fixed concept and target. -/
theorem experiment_refinement_gain_monotone
    {X C E E' Target : Type _} (q_C : Concept X C) (q_E : Concept X E)
    (q_E' : Concept X E') (target : X → Target) (refinement : Refines q_E q_E') :
    experimentGain q_C q_E target ⊆ experimentGain q_C q_E' target := by
  have joinedRefinement :
      Refines (conceptJoin q_C q_E) (conceptJoin q_C q_E') :=
    conceptJoin_refines_of_right_refines q_C q_E q_E' refinement
  have refinedDefectsSubset :
      targetDefects (conceptJoin q_C q_E') target ⊆
        targetDefects (conceptJoin q_C q_E) target :=
    targetDefects_antitone_of_refines
      (conceptJoin q_C q_E) (conceptJoin q_C q_E') target joinedRefinement
  simpa only [experimentGain] using
    (Set.sdiff_subset_sdiff_right refinedDefectsSubset)

/-- A finer experiment cannot reintroduce a target defect removed by a coarser one. -/
theorem refined_experiment_does_not_reintroduce_defect
    {X C E E' Target : Type _} (q_C : Concept X C) (q_E : Concept X E)
    (q_E' : Concept X E') (target : X → Target) (refinement : Refines q_E q_E')
    (pair : X × X) (baseDefect : pair ∈ targetDefects q_C target)
    (removed : pair ∉ targetDefects (conceptJoin q_C q_E) target) :
    pair ∉ targetDefects (conceptJoin q_C q_E') target := by
  have retainedGain : pair ∈ experimentGain q_C q_E' target :=
    experiment_refinement_gain_monotone q_C q_E q_E' target refinement
      ⟨baseDefect, removed⟩
  exact retainedGain.2

example :
    let q_C : Concept (Fin 3) Unit := fun _ => ()
    let q_E : Concept (Fin 3) Bool := fun x => decide (x = 0)
    let q_E' : Concept (Fin 3) (Fin 3) := id
    Refines q_E q_E' ∧
      experimentGain q_C q_E id ⊆ experimentGain q_C q_E' id ∧
      ((1, 2) : Fin 3 × Fin 3) ∈ experimentGain q_C q_E' id ∧
      ((1, 2) : Fin 3 × Fin 3) ∉ experimentGain q_C q_E id := by
  dsimp only
  have refinement :
      Refines (fun x : Fin 3 => decide (x = 0))
        (id : Concept (Fin 3) (Fin 3)) :=
    ⟨fun x => decide (x = 0), rfl⟩
  refine ⟨refinement, ?_, ?_, ?_⟩
  · exact experiment_refinement_gain_monotone
      (fun _ : Fin 3 => ()) (fun x => decide (x = 0)) id id refinement
  · simp [experimentGain, targetDefects, conceptJoin]
  · simp [experimentGain, targetDefects, conceptJoin]

#print axioms experiment_refinement_gain_monotone

end D5.S3.ConceptDynamics.Experiments.ExperimentRefinementGainMonotone
