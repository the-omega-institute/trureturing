import LeanInformationAudit.Tests.RegistrationGates.DeclaredBindings

namespace LeanInformationAudit.Tests.DeclaredDiagnostics
open Lean Meta TemplateBinding

private def observe (label : String) (ok : Bool) : MetaM Unit :=
  (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"

private def payload (record : BindingRecord) : Except String Json := do
  let .declaredUnresolved diagnostic := record.result | throw "expected unresolved"
  let parts := diagnostic.splitOn " provenance="
  unless parts.length == 2 do throw "missing provenance"
  let text := parts[1]!
  let value ← Json.parse text
  unless value.compress == text do throw "noncanonical provenance"
  return value

run_meta do
  let rows := records (← getEnv)
  let some valid := rows.find? (·.occurrence.key.theoremName == ``DeclaredBindings.validated)
    | throwError "setup: validated registration missing"
  let some absent := rows.find? (·.occurrence.key.theoremName == ``DeclaredBindings.undeclared)
    | throwError "setup: undeclared registration missing"
  let absentWire ← recordJson absent
  let expected := s!"IE-C050 ClosedTruthReadout key={absent.occurrence.key.root}/" ++
    s!"{absent.occurrence.key.catalog}/{absent.occurrence.key.theoremName} " ++
    "reason=unclassified_form rule=dtr.missing_declaration site=\"\" readout=\"\" " ++
    "provenance={\"argument_inputs\":[],\"extraction_inputs\":[],\"plan_identity\":null," ++
    "\"rule\":\"dtr.missing_declaration\",\"site\":\"\",\"template_key\":null}"
  observe "undeclared_diagnostic_retained" (
    absentWire.getObjValAs? String "diagnostic" == .ok expected &&
    (absentWire.getObjVal? "certificate").toOption.any (·.compress == "null"))
  let some descriptor := valid.descriptor | throwError "setup: descriptor missing"
  let claim : TemplateBindingClaim := {
    key := valid.occurrence.key, arena := valid.occurrence.arena,
    owner := valid.bindingOwner.getD (← getEnv).header.mainModule,
    descriptor := some (mkApp descriptor (mkConst ``Bool.true)) }
  let unresolved ← assess valid.occurrence (some claim)
  let details := (payload unresolved).toOption
  observe "unresolved_diagnostic_has_canonical_provenance" (details.any fun value =>
    value.getObjValAs? String "rule" == .ok "dtr.descriptor_telescope" &&
    value.getObjValAs? String "template_key" == .ok descriptor.getAppFn.constName!.toString &&
    (value.getObjValAs? String "plan_identity").toOption.any (·.length == 64) &&
    (value.getObjValAs? (Array Json) "extraction_inputs").toOption.any (·.size == 1) &&
    (value.getObjValAs? (Array Json) "argument_inputs").isOk)
  let incomplete ← assess valid.occurrence (some {
    claim with resolutionDiagnostic := some "incomplete_closure:E8.diagnostic_fixture" })
  observe "incomplete_diagnostic_has_null_provenance" (
    (payload incomplete).toOption.any (·.compress == "null"))
  let validWire ← recordJson valid
  observe "validated_diagnostic_absent" (
    validWire.getObjValAs? String "state" == .ok "declared_validated" &&
    (validWire.getObjVal? "diagnostic").toOption.any (·.compress == "null"))

end LeanInformationAudit.Tests.DeclaredDiagnostics
