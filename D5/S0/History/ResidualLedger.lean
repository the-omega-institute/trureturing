/- GID: D5/S0/History/ResidualLedger
   generality: G
   mirror-B: D5/B/S0/History/ResidualLedger
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Residual ledger entries are losslessly equivalent to their four typed components. -/

import Mathlib.Logic.Equiv.Prod

/- Provenance: pinned Mathlib supplies the standard equivalence bijectivity
   theorem (`Equiv.bijective`). The four-state residual workflow and its typed
   ledger entry are the source atom's additional data. -/

namespace D5.S0.History.ResidualLedger

/-- The four mutually exclusive states of a residual ledger entry. -/
inductive ResidualStatus where
  | open_
  | closed
  | tail
  | semantic
  deriving DecidableEq, Repr

/-- A residual entry records where the residual arose, which readout detects
it, its current status, and the next action or budget assigned to it. -/
structure ResidualLedgerEntry
    (Source Detector NextAction : Type*) where
  source : Source
  detector : Detector
  status : ResidualStatus
  nextAction : NextAction

/-- The component tuple named by the residual-ledger definition. -/
abbrev ResidualLedgerComponents
    (Source Detector NextAction : Type*) :=
  Source × Detector × ResidualStatus × NextAction

/-- Forget the field names without losing any residual-ledger component. -/
def residualLedgerEquivComponents
    (Source Detector NextAction : Type*) :
    ResidualLedgerEntry Source Detector NextAction ≃
      ResidualLedgerComponents Source Detector NextAction where
  toFun entry :=
    (entry.source, entry.detector, entry.status, entry.nextAction)
  invFun components :=
    { source := components.1
      detector := components.2.1
      status := components.2.2.1
      nextAction := components.2.2.2 }
  left_inv entry := by cases entry; rfl
  right_inv components := by
    rcases components with ⟨source, detector, status, nextAction⟩
    rfl

/-- The typed residual-ledger record contains exactly its source, detector,
four-state status, and next-action components. -/
theorem residual_ledger_components_bijective
    (Source Detector NextAction : Type*) :
    Function.Bijective
      (residualLedgerEquivComponents Source Detector NextAction) :=
  (residualLedgerEquivComponents Source Detector NextAction).bijective

end D5.S0.History.ResidualLedger
