/- GID: D5/S0/History/EmptyLedgerConservation
   generality: G
   mirror-B: D5/B/S0/History/EmptyLedgerConservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete detection discipline makes an empty open ledger exclude detectable residuals. -/

module
prelude
public import OmegaInit.Core

namespace D5.S0.History.EmptyLedgerConservation

open Omega

/-- A ledger satisfies detection discipline when every residual detectable at
an object is entered in that object's open ledger. -/
@[expose] public def LedgerDiscipline {Object : Type u} {Residual : Type v}
    (detectable openLedger : Object → Residual → Prop) : Prop :=
  ∀ object residual, detectable object residual → openLedger object residual

/-- Complete detection discipline makes an empty open ledger exclude detectable residuals. -/
public theorem empty_ledger_excludes_detectable_residual {Object : Type u} {Residual : Type v}
    (detectable openLedger : Object → Residual → Prop)
    (discipline : LedgerDiscipline detectable openLedger)
    {object : Object} (empty : ∀ residual, Not (openLedger object residual)) :
    Not (Exists (detectable object)) :=
  fun witness => witness.elim (fun residual detected =>
    empty residual (discipline object residual detected))

end D5.S0.History.EmptyLedgerConservation
