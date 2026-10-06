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

inductive OccurrenceCertificate where
  | positive (name : Name)
  | trivial (name : Name)
  deriving Inhabited, Repr, BEq

inductive CatalogVerdict where
  | irredundant (name : Name)
  | redundant (name : Name)
  deriving Inhabited, Repr, BEq

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

/-- Computed theorem data retained for summaries and the optional artifact. -/
structure SealTheoremRecord where
  theoremName : Name
  unitName : Name
  realizationName : Name
  certificate : OccurrenceCertificate
  closureCertificate : Option Name := none
  registrationModuleName : Name
  index : Nat
  primitiveCount : Nat
  primitiveAxes : Array String
  primitiveKernelAddress : String
  uniqueCaptureCount : Nat
  fullEscapeCount : Nat
  withoutEscapeCount : Nat
  roleSignatureHistogram : Array (String × Nat)
  proofMethod : String

deriving instance Inhabited, BEq for SealTheoremRecord

/-- Computed arena data retained for summaries and the optional artifact. -/
structure SealArenaRecord where
  catalog : CatalogRecord
  verdict : CatalogVerdict
  collisionClasses : Array (Array Name × Array Name) := #[]
  stateEnumeration : Option Name := none
  compiledEvidence : Bool := false
  proofMethod : String
  stateCard : Nat
  offDiagonalPairCount : Nat
  fullEscapeCount : Nat
  theorems : Array SealTheoremRecord
  deriving Inhabited, BEq

/-- Projections of imported, kernel-checked Reg fields. These local names are
output addresses; this extension is rebuilt from raw typed inputs each report. -/
structure CompiledSealEvidence where
  name : Name
  source : Name
  value : Expr

end LeanInformationAudit
