/- GID: D5/S0/History/EmptyLedgerConservation
   generality: G
   mirror-B: D5/B/S0/History/EmptyLedgerConservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete detection discipline makes an empty open ledger exclude detectable residuals. -/

import Mathlib.Data.Set.Basic

namespace D5.S0.History.EmptyLedgerConservation

/-- A ledger satisfies detection discipline when every residual detectable at
an object is entered in that object's open ledger. -/
def LedgerDiscipline {Object Residual : Type*}
    (detectable : Object → Residual → Prop)
    (openLedger : Object → Set Residual) : Prop :=
  ∀ x r, detectable x r → r ∈ openLedger x

/-- Under complete detection discipline, an object with an empty open ledger
has no detectable residual. This is a thin wrapper around mathlib's
`Set.eq_empty_iff_forall_notMem`, with discipline supplying ledger membership. -/
theorem empty_ledger_excludes_detectable_residual {Object Residual : Type*}
    (detectable : Object → Residual → Prop)
    (openLedger : Object → Set Residual)
    (discipline : LedgerDiscipline detectable openLedger)
    {x : Object} (hEmpty : openLedger x = ∅) :
    ¬∃ r, detectable x r := by
  rw [Set.eq_empty_iff_forall_notMem] at hEmpty
  rintro ⟨r, hr⟩
  exact hEmpty r (discipline x r hr)

end D5.S0.History.EmptyLedgerConservation
