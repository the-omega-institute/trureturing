import LeanInformationAudit.InputTypes

namespace LeanInformationAudit
open Lean

/-- A closed catalog and the canonical theorem-to-index assignment used by the seal. -/
structure CatalogUnitRecord where
  theoremName : Name
  unitName : Name
  realizationName : Name
  registrationModuleName : Name
  index : Nat
  deriving Inhabited, BEq

structure CatalogRecord where
  rootId : Name
  catalogId : CatalogId
  catalogKind : CatalogKind
  arenaName : Name
  catalogName : Name
  units : Array CatalogUnitRecord
  localSealNames : Bool
  deriving Inhabited, BEq

/-- Context-specific evidence for the single IE-C007 record. -/
inductive ZeroCaptureContext where
  | finite (full without : Nat) (stateEnumeration : Name)
  | structural (registration catalogSeal : Name)
  deriving Inhabited, BEq

structure ZeroCaptureRecord where
  root : Name
  theoremName : Name
  arena : Name
  catalog : Name
  index : Nat
  realization : Name
  trivialityCertificate : Name
  context : ZeroCaptureContext
  sameKernelCandidates : Array (Name × Nat × Name) := #[]
  closureCandidates : Array Name := #[]
  closureCertificate : Option Name := none
  deriving Inhabited, BEq

/-- The exact imported registration membership of a kernel-checked seal.
Mathematical obligations remain in Reg, without report statistics. -/
structure SealArenaRecord where
  catalog : CatalogRecord
  compiledEvidence : Bool := false
  deriving Inhabited, BEq

/-- Projections of imported, kernel-checked Reg fields. These local names are
output addresses; this extension is rebuilt from raw typed inputs each report. -/
structure CompiledSealEvidence where
  name : Name
  source : Name
  value : Expr

end LeanInformationAudit
