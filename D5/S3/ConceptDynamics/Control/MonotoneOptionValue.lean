/- GID: D5/S3/ConceptDynamics/Control/MonotoneOptionValue
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Control/MonotoneOptionValue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Monotone future value preserves inclusion between feasible futures. -/

import Mathlib.Data.Set.Basic
import Mathlib.Order.Monotone.Defs

/- Library-search audit trail (2026-08-25):
   * `rg -n -i 'MonotoneOptionValue|monotone_option_value|option value|future option'
     D5 Blueprint Golden/Frozen/accepted Meta/Digestion/formalizations` found no
     existing declaration for post-action feasible-future value.
   * A body-shape search for feasible or reachable sets built from transitions hit
     `Interventions.AttackSurfaceMonotonicity.Reach`, which is relational closure
     under a permission set rather than feasibility after a selected action.
   * Pinned Mathlib's exact order primitive is `Monotone`; applying that hypothesis
     directly to the displayed inclusion is the canonical proof.
   * The option sets are constructed publicly from `step` and `feasible`; no local
     definition or abbreviation duplicates a repository primitive or names a target.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Control.MonotoneOptionValue

/-- A monotone value of feasible futures cannot decrease when an action preserves
all futures available after another action. -/
theorem monotone_option_value
    {State Action Future Value : Type*} [Preorder Value]
    (step : Action -> State -> State) (feasible : State -> Future -> Prop)
    (value : Set Future -> Value) (valueMonotone : Monotone value)
    {u v : Action} {x : State}
    (optionInclusion :
      {future | feasible (step v x) future} <=
        {future | feasible (step u x) future}) :
    value {future | feasible (step v x) future} <=
      value {future | feasible (step u x) future} := by
  exact valueMonotone optionInclusion

#print axioms monotone_option_value

end D5.S3.ConceptDynamics.Control.MonotoneOptionValue
