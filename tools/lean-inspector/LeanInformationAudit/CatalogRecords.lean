import LeanInformationAudit.CatalogData
import Lean

namespace LeanInformationAudit
open Lean

private initialize compiledSealRecords : EnvExtension (Array SealArenaRecord) ←
  registerEnvExtension (pure #[])

def retainCompiledSealRecord (env : Environment) (record : SealArenaRecord) : Environment :=
  compiledSealRecords.modifyState env (·.push record)

def compiledSealRecordMatches (env : Environment) (record : SealArenaRecord) : Bool :=
  (compiledSealRecords.getState env).any (· == record)

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
