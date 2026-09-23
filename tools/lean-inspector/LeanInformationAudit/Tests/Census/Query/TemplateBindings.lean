import LeanInformationAudit.Census.Command
import LeanInformationAudit.Tests.RegistrationGates.DeclaredSidecar

namespace LeanInformationAudit.Tests.Census.Query.TemplateBindings
open Lean Meta CensusQuery DispositionCensus
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates DeclaredSidecarSource

information_theorem unresolved in arena
  readout via (missingTemplate (fun x : Bool => x))
  primitives (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm

private def observe (label : String) (ok : Bool) : MetaM Unit :=
  (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"

run_meta do
  let env ← getEnv
  let source := `LeanInformationAudit.Tests.RegistrationGates.DeclaredSidecarSource
  let sidecar := `LeanInformationAudit.Tests.RegistrationGates.DeclaredSidecar
  let some sourceIndex := env.getModuleIdx? source | throwError "setup: source not imported"
  let some sidecarIndex := env.getModuleIdx? sidecar | throwError "setup: sidecar not imported"
  let sourceWire ← do
    unsafe pure <| CensusStream.registryRecords source.toString
      env.header.moduleData[sourceIndex.toNat]!
  let sidecarWire ← do
    unsafe pure <| CensusStream.registryRecords sidecar.toString
      env.header.moduleData[sidecarIndex.toNat]!
  let sourceRows ← ofExcept <| sourceWire.getObjValAs? (Array Json) "finite"
  observe "census_registry_discovery_control" (sourceRows.size == 1)
  let sidecarRows ← ofExcept <| sidecarWire.getObjValAs? (Array Json) "bindings"
  observe "census_sidecar_discovered" (sidecarRows.size == 1 && sidecarRows.all fun row =>
    row.getObjValAs? String "module" == .ok sidecar.toString &&
      (row.getObjVal? "key").toOption.any
        (·.compress == (nameJson ``DeclaredSidecarSource.original).compress))
  let index ← indexScope env.header.mainModule
  let snapshot ← prepareBindingSnapshot #[source, sidecar]
  let joined ← bindingEvidence index ``DeclaredSidecarSource.original snapshot
  let rows ← ofExcept <| joined.getObjValAs? (Array Json) "records"
  for row in rows do
    if let .ok diagnostic := row.getObjValAs? String "diagnostic" then logInfo diagnostic
  observe "census_join_uses_validated_sidecar" (joined.getObjValAs? Bool "query_completed" == .ok true &&
    rows.size == 1 && rows.all fun row => row.getObjValAs? String "state" == .ok "declared_validated" &&
      row.getObjValAs? String "binding_source_path" == .ok (TemplateAudit.sourcePath sidecar))
  let missing ← prepareBindingSnapshot #[source, sidecar, `MissingGovernedBindingSidecar]
  let incomplete ← bindingEvidence index ``DeclaredSidecarSource.original missing
  observe "census_missing_sidecar_is_incomplete" (
    incomplete.getObjValAs? Bool "query_completed" == .ok false &&
    (incomplete.getObjValAs? String "diagnostic").toOption.any (·.contains "dtr.census_sidecar") &&
    (incomplete.getObjValAs? (Array Json) "records").toOption.any Array.isEmpty)
  let key : StatementKey := ⟨``unresolved,
    "sha256:000000000000000000000000000000000000000000000000000000000000002a"⟩
  let before ← assess index "fixture-head" key
  let unresolved ← bindingEvidence index key.theoremName snapshot
  let after ← assess index "fixture-head" key
  let rows ← ofExcept <| unresolved.getObjValAs? (Array Json) "records"
  observe "census_unresolved_preserves_mathematical_disposition" (
    before.className == after.className && before.className == "observed" &&
    unresolved.getObjValAs? Bool "query_completed" == .ok true && rows.size == 1 &&
    rows.all fun row => row.getObjValAs? String "state" == .ok "declared_unresolved" &&
      (row.getObjVal? "certificate").toOption.any (·.compress == "null"))

end LeanInformationAudit.Tests.Census.Query.TemplateBindings
