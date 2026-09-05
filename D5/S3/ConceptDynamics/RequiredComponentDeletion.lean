/- GID: D5/S3/ConceptDynamics/RequiredComponentDeletion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RequiredComponentDeletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Removing one component preserves theorem eligibility exactly when the theorem was eligible before removal and did not require that component. -/

import Mathlib.Data.Set.Lattice

/- Library-search audit trail (2026-09-04):
   * Searches across D5 for component eligibility, required-component deletion,
     load-bearing coordinates, dependency removal, and generalized closure laws
     found no exact theorem. `DependencyClosureAdmissionAntitone` is adjacent but
     concerns evidence contamination under enlarged closures, not removal from a
     presentation that must contain every required component.
   * Pinned Mathlib supplies `Set.diff` and singleton membership. No packaged
     theorem states the quantified eligibility equivalence below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RequiredComponentDeletion

/-- A theorem remains eligible after deleting `component` exactly when it was
eligible before deletion and does not require that component. This is an iff:
the forward direction detects a genuinely load-bearing component, while the
reverse direction proves deletion is harmless when the requirement is absent. -/
theorem required_component_deletion_iff
    {Component TheoremName : Type*}
    (requires : TheoremName -> Component -> Prop)
    (present : Set Component) (theoremName : TheoremName) (component : Component) :
    (forall candidate, requires theoremName candidate ->
        candidate ∈ present \ {component}) ↔
      (forall candidate, requires theoremName candidate -> candidate ∈ present) ∧
        ¬ requires theoremName component := by
  constructor
  · intro eligibleAfter
    constructor
    · intro candidate required
      exact (eligibleAfter candidate required).1
    · intro required
      exact (eligibleAfter component required).2 rfl
  · rintro ⟨eligibleBefore, notRequired⟩ candidate required
    refine ⟨eligibleBefore candidate required, ?_⟩
    intro same
    subst candidate
    exact notRequired required

/-- The deletion law is strict, not vacuous: on a concrete two-component
presentation, deleting the required Boolean component destroys eligibility. -/
theorem required_component_deletion_can_be_strict :
    exists requires : Unit -> Bool -> Prop, exists present : Set Bool,
      (forall component, requires () component -> component ∈ present) ∧
        requires () true ∧
        ¬ (forall component, requires () component ->
            component ∈ present \ {true}) := by
  refine ⟨fun _ component => component = true, Set.univ, ?_⟩
  simp

#print axioms required_component_deletion_iff
#print axioms required_component_deletion_can_be_strict

end D5.S3.ConceptDynamics.RequiredComponentDeletion
