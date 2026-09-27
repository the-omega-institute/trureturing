import LeanInformationAudit.Census.Command
import LeanInformationAudit.Tests.RegistrationGates.DeclaredRegistration

namespace LeanInformationAudit.Tests.Census.Query.TemplateBindings
open Lean Meta CensusQuery DispositionCensus
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates DeclaredSource

information_theorem unresolved in arena
  readout via (missingTemplate (fun x : Bool => x))
  primitives (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm

private def observe (label : String) (ok : Bool) : MetaM Unit :=
  (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"

run_meta do
  let env ← getEnv
  let source := `LeanInformationAudit.Tests.RegistrationGates.DeclaredSource
  let registration := `LeanInformationAudit.Tests.RegistrationGates.DeclaredRegistration
  let some sourceIndex := env.getModuleIdx? source | throwError "setup: source not imported"
  let some registrationIndex := env.getModuleIdx? registration | throwError "setup: registration not imported"
  let sourceWire ← do
    unsafe pure <| CensusStream.registryRecords source.toString
      env.header.moduleData[sourceIndex.toNat]!
  let registrationWire ← do
    unsafe pure <| CensusStream.registryRecords registration.toString
      env.header.moduleData[registrationIndex.toNat]!
  let sourceRows ← ofExcept <| sourceWire.getObjValAs? (Array Json) "finite"
  observe "census_mathematical_source_has_no_registrations" (sourceRows.isEmpty)
  let registrationRows ← ofExcept <| registrationWire.getObjValAs? (Array Json) "bindings"
  observe "census_registration_discovered" (registrationRows.size == 2 && registrationRows.all fun row =>
    row.getObjValAs? String "module" == .ok registration.toString &&
      (row.getObjVal? "key").toOption.any
        (·.compress == (nameJson ``DeclaredSource.original).compress))
  let index ← indexScope env.header.mainModule
  let snapshot ← prepareBindingSnapshot #[source, registration]
  let joined ← bindingEvidence index ``DeclaredSource.original snapshot
  let rows ← ofExcept <| joined.getObjValAs? (Array Json) "records"
  for row in rows do
    if let .ok diagnostic := row.getObjValAs? String "diagnostic" then logInfo diagnostic
  observe "census_join_uses_validated_registration" (joined.getObjValAs? Bool "query_completed" == .ok true &&
    rows.size == 1 && rows.all fun row => row.getObjValAs? String "state" == .ok "declared_validated" &&
      row.getObjValAs? String "binding_source_path" == .ok (TemplateAudit.sourcePath registration))
  let missing ← prepareBindingSnapshot #[source, registration, `MissingGovernedBindingRegistration]
  let incomplete ← bindingEvidence index ``DeclaredSource.original missing
  observe "census_missing_registration_is_incomplete" (
    incomplete.getObjValAs? Bool "query_completed" == .ok false &&
    (incomplete.getObjValAs? String "diagnostic").toOption.any (·.contains "dtr.census_registration") &&
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
