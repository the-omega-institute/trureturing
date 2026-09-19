import LeanInformationAudit.Tests.RegistrationGates.DeclaredBindings
import LeanInformationAudit.Tests.RegistrationGates.DeclaredStructural
import LeanInformationAudit.Tests.SourceIsolation

namespace LeanInformationAudit.Tests.DeclaredExport
open Lean Meta Elab Command TemplateBinding

run_meta do
  let snapshot ← exportSnapshot
  let expected := #[
    `LeanInformationAudit.Tests.DeclaredBindings.validated,
    `LeanInformationAudit.Tests.DeclaredBindings.unresolved,
    `LeanInformationAudit.Tests.DeclaredBindings.undeclared,
    `LeanInformationAudit.Tests.DeclaredStructural.declared,
    `LeanInformationAudit.Tests.DeclaredStructural.undeclared]
  unless snapshot.selected.size == expected.size &&
      expected.all (fun name => snapshot.selected.any (·.occurrence.key.theoremName == name)) do
    throwError "setup: export inventory differs from the five independent occurrences"
  let modules := #[`LeanInformationAudit.Tests.RegistrationGates.DeclaredBindings,
      `LeanInformationAudit.Tests.RegistrationGates.DeclaredStructural].map fun moduleName =>
    (moduleName, snapshot.originals.filter (·.occurrence.key.registrationModule == moduleName)
      |>.map (·.occurrence.key))
  let wires ← reportJson modules
  unless wires.size == modules.size do throwError "setup: export lost a module"
  for ((_, registered), wire) in modules.zip wires do
    let .ok rows := wire.getObjValAs? (Array Json) "records"
      | throwError "setup: missing record wire"
    unless rows.size == registered.size do throwError "setup: export partition lost a row"
  logInfo "[PASS] complete_producer_loader_wire"
  IO.FS.createDirAll ".lake/build"
  IO.FS.writeFile ".lake/build/declared-template-evidence.json" ((Json.arr wires).compress ++ "\n")
  LeanInformationAudit.Tests.withPrivateSources do
    let manifestPath := "lean-report-inputs.json"
    let original ← IO.FS.readFile manifestPath
    let .ok manifest := Json.parse original | throwError "setup: invalid manifest"
    let .ok fields := manifest.getObj? | throwError "setup: manifest is not an object"
    IO.FS.writeFile manifestPath ((Json.mkObj (fields.toList.map fun (key, value) =>
      (key, if key == "report_semantic_version" then toJson (9 : Nat) else value))).compress)
    let bumped ← reportJson modules
    let accepted := bumped.all fun wire => wire.getObjValAs? Nat "compatibility_version" == .ok 9
    (if accepted then logInfo else logError)
      m!"[{if accepted then "PASS" else "FAIL"}] manifest_only_bump_emits_nine"
    for (label, text) in #[("missing", "{}"), ("string", "{\"report_semantic_version\":\"7\"}"),
        ("zero", "{\"report_semantic_version\":0}"), ("negative", "{\"report_semantic_version\":-1}"),
        ("boolean", "{\"report_semantic_version\":true}"), ("fraction", "{\"report_semantic_version\":6.5}"),
        ("json", "{"), ("absent", "")] do
      if label == "absent" then IO.FS.removeFile manifestPath else IO.FS.writeFile manifestPath text
      let rejected ← try
        discard <| reportJson modules
        pure false
      catch error => pure ((← error.toMessageData.toString).contains "DTR-ManifestVersion")
      (if rejected then logInfo else logError)
        m!"[{if rejected then "PASS" else "FAIL"}] invalid_manifest_version_rejected_{label}"

end LeanInformationAudit.Tests.DeclaredExport
