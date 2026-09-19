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
    let .ok version := manifest.getObjValAs? Nat "report_semantic_version"
      | throwError "setup: missing manifest version"
    let manifestInputs := fun (rows : Array Json) => rows.mapM fun wire => do
      let .ok inputs := wire.getObjValAs? (Array Json) "inputs"
        | throwError "setup: missing source inputs"
      let bindings := inputs.filter fun input =>
        input.getObjValAs? String "path" == .ok manifestPath
      unless bindings.size == 1 do throwError "setup: manifest binding is not unique"
      let .ok sha256 := bindings[0]!.getObjValAs? String "sha256"
        | throwError "setup: missing manifest digest"
      pure ({ path := manifestPath, sha256 } : TemplateAudit.SourceInput)
    let previousInputs ← manifestInputs wires
    let originalHash := Sha256.hex original.toUTF8
    unless previousInputs.all (·.sha256 == originalHash) do
      throwError "setup: original wire does not bind manifest bytes"
    let changed := original ++ "\n"
    let currentHash := Sha256.hex changed.toUTF8
    IO.FS.writeFile manifestPath changed
    let rejected ← try
      TemplateAudit.validateSourceInputs previousInputs
      pure false
    catch error => pure ((← error.toMessageData.toString).contains
      "incomplete_closure:E7.stale_source:lean-report-inputs.json")
    (if rejected then logInfo else logError)
      m!"[{if rejected then "PASS" else "FAIL"}] manifest_byte_change_rejects_old_binding"
    let refreshed ← reportJson modules
    let currentInputs ← manifestInputs refreshed
    let rebound := currentHash != originalHash && currentInputs.size == modules.size &&
      currentInputs.all (·.sha256 == currentHash)
    (if rebound then logInfo else logError)
      m!"[{if rebound then "PASS" else "FAIL"}] manifest_byte_change_binds_current_bytes"
    let sameVersion := refreshed.all fun wire =>
      wire.getObjValAs? Nat "compatibility_version" == .ok version
    (if sameVersion then logInfo else logError)
      m!"[{if sameVersion then "PASS" else "FAIL"}] manifest_byte_change_preserves_compatibility"
    IO.FS.writeFile manifestPath ((Json.mkObj (fields.toList.map fun (key, value) =>
      (key, if key == "report_semantic_version" then toJson (8 : Nat) else value))).compress)
    let bumped ← reportJson modules
    let accepted := bumped.all fun wire => wire.getObjValAs? Nat "compatibility_version" == .ok 8
    (if accepted then logInfo else logError)
      m!"[{if accepted then "PASS" else "FAIL"}] manifest_only_bump_emits_eight"
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
