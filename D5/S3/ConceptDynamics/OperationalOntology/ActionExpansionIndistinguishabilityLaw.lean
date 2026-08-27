/- GID: D5/S3/ConceptDynamics/OperationalOntology/ActionExpansionIndistinguishabilityLaw
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/OperationalOntology/ActionExpansionIndistinguishabilityLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A separating new action can make indistinguishability shrink strictly. -/

import D5.S3.ConceptDynamics.OperationalOntology.ActionExpansionIndistinguishability

/- Library-search audit trail (2026-08-27):
   * The exact D5 hit for the forward inclusion is the frozen theorem
     `action_expansion_shrinks_indistinguishability`, imported and applied below.
   * Repository searches for an action-expansion new-action clause or a public
     converse countermodel found no declaration; the predecessor states its
     Boolean countermodel only as an unnamed example.
   * Pinned Mathlib provides exact membership elimination for bounded
     intersections as `Set.mem_iInter₂` in `Mathlib.Data.Set.Lattice`; it is
     applied to the expanded relation below.
   * Pinned Mathlib has no theorem packaging the forward inclusion, the
     new-action separation implication, and a shared explicit countermodel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.OperationalOntology.ActionExpansionIndistinguishabilityLaw

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.OperationalOntology.ActionExpansionIndistinguishability

/-- Enlarging an action set shrinks behavioral indistinguishability; any newly
available action that separates an originally indistinguishable pair removes
that pair, and the reverse inclusion fails in an explicit finite model. -/
theorem action_expansion_indistinguishability_law
    {Action State Output : Type _}
    (original expanded : Set Action) (act : Action -> State -> State)
    (observe : Concept State Output) (hExpansion : original ⊆ expanded) :
    actionIndistinguishability expanded act observe ⊆
        actionIndistinguishability original act observe ∧
      (∀ action : Action, action ∈ expanded \ original ->
        ∀ pair : {pair : State × State //
          pair ∈ actionIndistinguishability original act observe},
          observe (act action pair.1.1) ≠ observe (act action pair.1.2) ->
            pair.1 ∉ actionIndistinguishability expanded act observe) ∧
      ∃ (counterOriginal counterExpanded : Set Unit)
          (counterAct : Unit -> Bool -> Bool)
          (counterObserve : Concept Bool Bool) (x y : Bool),
        counterOriginal ⊂ counterExpanded ∧
          (x, y) ∈ actionIndistinguishability
            counterOriginal counterAct counterObserve ∧
          (x, y) ∉ actionIndistinguishability
            counterExpanded counterAct counterObserve := by
  constructor
  · exact action_expansion_shrinks_indistinguishability
      original expanded act observe hExpansion
  constructor
  · intro action hAction pair hSeparates hExpanded
    apply hSeparates
    exact Set.mem_iInter₂.mp hExpanded action hAction.1
  · refine ⟨∅, {()}, fun _ => id, id, false, true, ?_⟩
    simp [actionIndistinguishability, Set.ssubset_iff_subset_ne]

#print axioms action_expansion_indistinguishability_law

end D5.S3.ConceptDynamics.OperationalOntology.ActionExpansionIndistinguishabilityLaw
