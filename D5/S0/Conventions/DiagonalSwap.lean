/- GID: D5/S0/Conventions/DiagonalSwap
   generality: G
   mirror-B: D5/B/S0/Conventions/DiagonalSwap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Boolean swap changes every value selected along a self-application diagonal. -/

import Mathlib.Data.Bool.Basic

namespace D5.S0.Conventions.DiagonalSwap

/-- Applying the Boolean swap to a value selected on the self-application
diagonal changes that value. -/
theorem swap_changes_self_diagonal {Index : Type*} (assignment : Index -> Index -> Bool) :
    forall index, Not (Bool.not (assignment index index) = assignment index index) := by
  intro index
  exact Bool.not_ne_self (assignment index index)

/-- A concrete inhabited index domain for the diagonal statement. -/
example : Nonempty PUnit := inferInstance

/-- Boolean-valued binary assignments exist on an inhabited index domain. -/
example : Nonempty (PUnit -> PUnit -> Bool) := ⟨fun _ _ => false⟩

end D5.S0.Conventions.DiagonalSwap
