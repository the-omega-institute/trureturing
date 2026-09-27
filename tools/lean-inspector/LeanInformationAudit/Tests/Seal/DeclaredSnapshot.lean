import LeanInformationAudit.Tests.RegistrationGates.DeclaredTemplates
import LeanInformationAudit.SealCommand

namespace LeanInformationAudit.Tests.DeclaredSnapshot
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

register_information_template cutRealization

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ x : Bool, r.readout () x = x.not.not

instance : DecidableEq arena.State := instDecidableEqBool

information_theorem selected in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  primitives (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm

expect_information_occurrence selected in arena
  from "LeanInformationAudit.Tests.Seal.DeclaredSnapshot"

private def observe (label : String) (ok : Bool) : CommandElabM Unit :=
  (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"

private def counts : CommandElabM (Nat × Nat) := do
  let env ← getEnv
  return ((observedSourceValidations env).size, (TemplateBinding.observedAssessments env).size)

-- Both entry points validate sources once and reuse existing binding evidence.
-- Snapshots are tested in independent restored command states, with a fixed
-- single-occurrence oracle rather than a count derived from the registry.
run_cmd do
  let saved ← get
  let before ← counts
  let catalogs ← prepareCatalogs
  let after ← counts
  let independent := catalogs.size == 1 && after.1 - before.1 == 1 && after.2 == before.2
  set saved
  let before ← counts
  prepareSealPublication
  let after ← counts
  let published := (SealRecords.forRoot (← getEnv) (← getEnv).header.mainModule).size == 1
  let once := after.1 - before.1 == 1 && after.2 == before.2
  set saved
  observe "seal_binding_audit_at_most_once" (independent && once)
  -- This independent positive checks functional output. The mutation-sensitive
  -- invocation contract belongs to the preceding label alone.
  observe "both_seal_callers_validate_once" (catalogs.size == 1 && published)

run_cmd do
  let saved ← get
  let entries := InformationRegistry.entries (← getEnv)
  let snapshot ← validateSourceSnapshot entries
  let root := (← getEnv).header.mainModule
  let qualified := entries.map fun entry => { entry with
    unitName := catalogQualifiedName root entry.canonicalObjectArenaName
      entry.effectiveCatalogId entry.theoremName theoremUnitSuffix
    realizationName := catalogQualifiedName root entry.canonicalObjectArenaName
      entry.effectiveCatalogId entry.theoremName primitiveRealizationSuffix }
  let snapshot ← snapshot.stageAliases qualified
  let catalogs ← prepareCatalogsFromSnapshot snapshot
  let env ← getEnv
  let aliasesPresent := qualified.all fun entry =>
    env.contains entry.unitName && env.contains entry.realizationName
  set saved
  observe "seal_checked_alias_extension_accepted" (catalogs.size == 1 && aliasesPresent)

run_cmd do
  let saved ← get
  let snapshot ← validateSourceSnapshot (InformationRegistry.entries (← getEnv))
  elabCommand (← `(command| def snapshotExtra : Bool := true))
  let rejected ← try
    let _ ← prepareCatalogsFromSnapshot snapshot
    pure false
  catch error =>
    pure (((← error.toMessageData.toString).splitOn "rule=dtr.snapshot_environment").length == 2)
  set saved
  observe "seal_snapshot_stale_input_rejected" rejected

run_cmd do
  let saved ← get
  let entries := InformationRegistry.entries (← getEnv)
  let snapshot ← validateSourceSnapshot entries
  let wrong := entries.map fun entry => { entry with statementIdentity := "changed" }
  let rejected ← try
    let _ ← snapshot.stageAliases wrong
    pure false
  catch error =>
    pure (((← error.toMessageData.toString).splitOn "rule=dtr.snapshot_correspondence").length == 2)
  set saved
  observe "seal_snapshot_wrong_correspondence_rejected" rejected

end LeanInformationAudit.Tests.DeclaredSnapshot
