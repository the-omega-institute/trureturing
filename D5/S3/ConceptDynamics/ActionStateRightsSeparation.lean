/- GID: D5/S3/ConceptDynamics/ActionStateRightsSeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ActionStateRightsSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Empty action states separate non-infringement from positive realization. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Data.Set.Lattice

/- Library-search audit trail (2026-08-21):
   * `rg -n 'negativeRight|positiveRight|U_x|action state' D5 --glob '*.lean'`
     found no declaration packaging the source's two right predicates.
   * Pinned Mathlib supplies `Set.Disjoint` and the empty-set membership
     lemmas used directly below; no theorem combines the two source clauses.
   * The family import is retained for the canonical Concept namespace; the
     action, choice, and goal carriers below are constructed from the source
     primitives rather than from a target-shaped definition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ActionStateRightsSeparation

/-- A negative right forbids an action from the actions actually chosen. -/
def negativeRight {Action : Type*}
    (forbidden chosen : Set Action) : Prop :=
  Disjoint forbidden chosen

/-- A positive right requires an allowed action whose transition reaches the
goal set. -/
def positiveRight {State Action : Type*}
    (allowed : Set Action) (step : Action → State → State)
    (goal : Set State) (state : State) : Prop :=
  ∃ action, action ∈ allowed ∧ step action state ∈ goal

/-- With no allowed action, every prohibited subset is harmless while the
positive goal cannot be reached; the two rights are not opposite forms of one
permission predicate. -/
theorem no_action_state_separates_rights
    {State Action : Type*}
    (state : State) (allowed chosen : Set Action)
    (step : Action → State → State) (goal : Set State)
    (chosenAllowed : chosen ⊆ allowed)
    (allowedEmpty : allowed = ∅)
    (outside : state ∉ goal) :
    (∀ forbidden : Set Action,
      forbidden ⊆ allowed → negativeRight forbidden chosen) ∧
      ¬ positiveRight allowed step goal state ∧
      ¬ (state ∈ goal ∨ positiveRight allowed step goal state) ∧
      ¬((∀ forbidden : Set Action,
          forbidden ⊆ allowed → negativeRight forbidden chosen) ↔
        positiveRight allowed step goal state) := by
  have chosenEmpty : chosen = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro action hChosen
    have hAllowed := chosenAllowed hChosen
    rw [allowedEmpty] at hAllowed
    exact hAllowed
  have noForbidden :
      ∀ forbidden : Set Action,
        forbidden ⊆ allowed → negativeRight forbidden chosen := by
    intro forbidden _
    simp [negativeRight, chosenEmpty]
  have noPositive : ¬ positiveRight allowed step goal state := by
    intro hPositive
    rcases hPositive with ⟨action, hAllowed, _⟩
    rw [allowedEmpty] at hAllowed
    exact hAllowed
  refine ⟨noForbidden, noPositive, ?_, ?_⟩
  · intro hRealized
    rcases hRealized with hInGoal | hPositive
    · exact outside hInGoal
    · exact noPositive hPositive
  · intro hEquivalent
    exact noPositive (hEquivalent.mp noForbidden)

/-- The public hypotheses and four conclusions hold in a two-state model. -/
example :
    (∀ forbidden : Set Unit,
      forbidden ⊆ (∅ : Set Unit) → negativeRight forbidden ∅) ∧
      ¬ positiveRight (∅ : Set Unit) (fun _ state => state) {true} false ∧
      ¬ (false ∈ ({true} : Set Bool) ∨
        positiveRight (∅ : Set Unit) (fun _ state => state) {true} false) ∧
      ¬((∀ forbidden : Set Unit,
          forbidden ⊆ (∅ : Set Unit) → negativeRight forbidden ∅) ↔
        positiveRight (∅ : Set Unit) (fun _ state => state) {true} false) := by
  exact no_action_state_separates_rights
    (state := false) (allowed := ∅) (chosen := ∅)
    (step := fun (_ : Unit) state => state) (goal := {true})
    (by simp) rfl (by simp)

#print axioms no_action_state_separates_rights

end D5.S3.ConceptDynamics.ActionStateRightsSeparation
