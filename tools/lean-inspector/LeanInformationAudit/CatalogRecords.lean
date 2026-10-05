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

private initialize compiledSealRecords : EnvExtension (Array SealArenaRecord) ←
  registerEnvExtension (pure #[])

def retainCompiledSealRecord (env : Environment) (record : SealArenaRecord) : Environment :=
  compiledSealRecords.modifyState env (·.push record)

def compiledSealRecordMatches (env : Environment) (record : SealArenaRecord) : Bool :=
  (compiledSealRecords.getState env).any (· == record)

/-- Projections of imported, kernel-checked Reg fields. These local names are
output addresses; this extension is rebuilt from raw typed inputs each report. -/
structure CompiledSealEvidence where
  name : Name
  source : Name
  value : Expr

private initialize compiledSealEvidence : EnvExtension (Array CompiledSealEvidence) ←
  registerEnvExtension (pure #[])

def compiledSealEvidence? (env : Environment) (name : Name) : Option Expr :=
  (compiledSealEvidence.getState env).find? (·.name == name) |>.map (·.value)

def compiledSealEvidenceSource? (env : Environment) (name : Name) : Option Name :=
  (compiledSealEvidence.getState env).find? (·.name == name) |>.map (·.source)

def retainCompiledSealEvidence (env : Environment) (name source : Name) (value : Expr) : Environment :=
  compiledSealEvidence.modifyState env (·.push { name, source, value })

def resolveSealEvidence (name : Name) : Meta.MetaM Expr := do
  if let some value := compiledSealEvidence? (← getEnv) name then return value
  Meta.mkConstWithFreshMVarLevels name

def hasSealEvidence (env : Environment) (name : Name) : Bool :=
  env.contains name || (compiledSealEvidence? env name).isSome

end LeanInformationAudit
