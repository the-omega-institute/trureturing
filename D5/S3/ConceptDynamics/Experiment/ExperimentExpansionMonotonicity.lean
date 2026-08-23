/- GID: D5/S3/ConceptDynamics/Experiment/ExperimentExpansionMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/ExperimentExpansionMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Expanding the experiment set shrinks indistinguishability and can reveal states. -/

import Mathlib.Data.Set.Lattice

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'expansion_shrinks_indistinguishability' D5 Golden/Frozen/accepted`
     found the frozen action-factorized result
     `ActionExpansionIndistinguishability.action_expansion_shrinks_indistinguishability`.
     It requires a state action followed by one fixed readout, so it does not cover an
     arbitrary family `run : Experiment -> State -> Response`.
   * `rg -in 'Indist|indistinguish|∀ e ∈|Set.Subset' D5/S3/ConceptDynamics/`
     found that action result and unrelated faithfulness/refinement modules.
     `FiniteObservationRefinementBound` concerns depths of one iterated update, not
     enlargement of an arbitrary experiment family, and supplies no matching witness.
   * Pinned Mathlib contains the exact range-restriction lemma
     `Set.biInter_subset_biInter_left` in `Mathlib.Data.Set.Lattice`; it is applied below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Experiment.ExperimentExpansionMonotonicity

/-- State pairs receiving equal responses from every currently allowed experiment. -/
def experimentIndistinguishability {Experiment State Response : Type _}
    (allowed : Set Experiment) (run : Experiment -> State -> Response) :
    Set (State × State) :=
  ⋂ experiment ∈ allowed,
    {pair | run experiment pair.1 = run experiment pair.2}

/-- Enlarging the allowed experiment set can only remove indistinguishable state pairs. -/
theorem expansion_shrinks_indistinguishability
    {Experiment State Response : Type _}
    (original expanded : Set Experiment) (run : Experiment -> State -> Response)
    (hExpansion : original ⊆ expanded) :
    experimentIndistinguishability expanded run ⊆
      experimentIndistinguishability original run := by
  unfold experimentIndistinguishability
  exact Set.biInter_subset_biInter_left hExpansion

/-- Adding the identity experiment makes the two Boolean states publicly distinguishable. -/
example :
    (∅ : Set Unit) ⊆ {()} ∧
      (false, true) ∈ experimentIndistinguishability (∅ : Set Unit) (fun _ => id) ∧
      (false, true) ∉ experimentIndistinguishability ({()} : Set Unit) (fun _ => id) := by
  simp [experimentIndistinguishability]

#print axioms expansion_shrinks_indistinguishability

end D5.S3.ConceptDynamics.Experiment.ExperimentExpansionMonotonicity
