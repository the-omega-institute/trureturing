import LeanInformationAuditInterface.RootContract

namespace LeanInformationAudit

open Lean

/-- An independently enumerated, identified source snapshot. -/
structure InformationSourceSnapshot where
  sourceIdentity : String
  sourceRevision : String
  enumeratorIdentity : String
  moduleCount : Nat
  occurrences : Array SnapshotOccurrence
  deriving Inhabited, Repr

end LeanInformationAudit
