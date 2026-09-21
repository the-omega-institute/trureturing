import Lean

namespace LeanInformationAudit
open Lean

/-- Producer-captured identities; no field is derived in the consuming root. -/
structure SnapshotOccurrence where
  objectArenaName : Name
  theoremName : Name
  statementIdentity : String
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

end LeanInformationAudit
