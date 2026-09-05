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

end LeanInformationAudit
