import Lean

namespace LeanInformationAudit
open Lean

/-- Independent expected rows retain either a supplied identity or the original
compiler expression. The report interprets the expression; the recorder does not hash it. -/
structure SnapshotOccurrence where
  objectArenaName : Name
  theoremName : Name
  statementIdentity : String := ""
  capturedStatement : Option Expr := none
  registrationModuleName : Name
  deriving Inhabited, Repr

/-- An independently enumerated, identified source snapshot. -/
structure InformationSourceSnapshot where
  sourceIdentity : String
  sourceRevision : String
  enumeratorIdentity : String
  moduleCount : Nat
  occurrences : Array SnapshotOccurrence
  deriving Inhabited, Repr

/-- Independently supplied seal expectations and generated-name ownership.
`source` must retain `baseline`; `expected` is the exact registry to seal.
None keeps imported companions private to the compiling module; an explicit
prefix publishes genuine qualified declarations for downstream consumers. -/
structure RootCatalogContract where
  rootId : Name
  expected : Array SnapshotOccurrence
  source : Array SnapshotOccurrence
  baseline : Array SnapshotOccurrence := #[]
  companionPrefix : Option Name := none
  deriving Inhabited

/-- Capture the original compiler type before registration and assessment. -/
def captureStatement (env : Environment) (name : Name) : Option Expr :=
  (env.find? name).map (·.type)

end LeanInformationAudit
