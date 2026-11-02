module

public import Lean.Elab.Deriving
public meta import Lean.Elab.Deriving
public import Mathlib.Tactic.DeriveFintype
meta import all Lean.Elab.Deriving.DecEq
meta import all Lean.Elab.Deriving.BEq
meta import all Lean.Elab.Deriving.Ord

/-! The allowlist calls only the pinned Lean and Mathlib handlers, never a registry extended
by an imported delivery. -/
public meta section
namespace LeanInformationAudit.SearchReduction
open Lean

def pinnedDerivingHandlers : Array (Name × Elab.DerivingHandler) := #[
  (``DecidableEq, Elab.Deriving.DecEq.mkDecEqInstanceHandler),
  (``Repr, Elab.Deriving.Repr.mkReprInstanceHandler),
  (``Inhabited, Elab.Deriving.mkInhabitedInstanceHandler),
  (``BEq, Elab.Deriving.BEq.mkBEqInstanceHandler),
  (``Ord, Elab.Deriving.Ord.mkOrdInstanceHandler),
  (``Hashable, Elab.Deriving.Hashable.mkHashableHandler),
  (``Nonempty, Elab.Deriving.mkNonemptyInstanceHandler),
  (``Fintype, Mathlib.Deriving.Fintype.mkFintypeInstanceHandler)]

def pinnedDerivingClasses : Array Name := pinnedDerivingHandlers.map (·.1)

def pinnedDeriving (cls : Name) (owners : Array Name) : Elab.Command.CommandElabM Bool := do
  let some (_, handler) := pinnedDerivingHandlers.find? (·.1 == cls) | return false
  handler owners

end LeanInformationAudit.SearchReduction
