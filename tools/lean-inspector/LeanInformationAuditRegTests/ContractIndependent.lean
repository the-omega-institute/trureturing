import LeanInformationAudit.ContractPrototype.Replay

namespace LeanInformationAuditRegTests.ContractIndependent
open Lean Meta Elab Command LeanInformationAudit

/-- Generated declarations form a name-keyed inventory. Preserve duplicate
detection and compare each declaration's owner, kind, universes, type and body. -/
def generatedInventory (names : Array Name) : MetaM Json := do
  let sorted := names.qsort Name.quickLt
  unless (NameSet.ofArray names).toArray.size == names.size do
    throwError "independent_duplicate_generated_name"
  let entries ← sorted.mapM fun name => do
    let info ← getConstInfo name
    let type ← ofExcept <| TemplateAudit.rawStatementIdentity info.levelParams info.type
    let body ← info.value? (allowOpaque := true) |>.mapM fun value =>
      ofExcept <| TemplateAudit.rawStatementIdentity info.levelParams value
    return Json.mkObj [
      ("name", toJson name.toString),
      ("owner", toJson (GeneratedDeclarations.ownerOf (← getEnv) name).toString),
      ("theorem", toJson info.isTheorem), ("universes", toJson (info.levelParams.map Name.toString)),
      ("type_identity", toJson type.1), ("body_identity", toJson (body.map Prod.fst))]
  return Json.arr entries

/-- Each caller imports one target in a fresh process. The source environment
contains only that target's closure; the report separately loads the fixed judge.
No environment from another target or the batch is reused. -/
def verify (target : Name) : CommandElabM Unit := do
  let driver := (← getEnv).setExporting false
  let some reference ← IO.getEnv "STRATALINT_CONTRACT_PROTOTYPE_REFERENCE"
    | throwError "independent_reference_missing"
  let some output ← IO.getEnv "STRATALINT_CONTRACT_PROTOTYPE_OUTPUT"
    | throwError "independent_output_missing"
  let document ← ofExcept <| Json.parse (← IO.FS.readFile reference)
  let rows ← ofExcept <| document.getObjValAs? (Array Json) "rows"
  let some expectedRow := rows.find? (fun row =>
      (row.getObjValAs? String "target").toOption == some target.toString)
    | throwError "independent_reference_target_missing:{target}"
  let reading ← liftTermElabM do
    let expected := (reachableModules driver target).toArray.qsort Name.quickLt
    let sourceCount ← unsafe withImportModules #[{ module := target }] {} (trustLevel := 0)
      fun sourceEnv => do
        let actual := sourceEnv.header.moduleNames.qsort Name.quickLt
        unless actual == expected do
          throw <| IO.userError s!"single_import_closure_mismatch:{target}"
        return actual.size
    let reportModules := driver.header.moduleNames.qsort Name.quickLt
    let judgeModules := reachableModules driver `LeanInformationAuditRegTests.ContractIndependent
    let reportExpected := (expected ++ judgeModules.toArray)
      |> NameSet.ofArray |>.toArray.qsort Name.quickLt
    unless reportModules == reportExpected do throwError "single_report_closure_mismatch:{target}"
    setEnv driver
    let reports ← ContractPrototype.reports #[target]
    let some (binding, generated, assessed) := reports[0]?
      | throwError "independent_report_missing:{target}"
    setEnv assessed
    let inventory ← generatedInventory generated
    let rawOrderEqual := toJson (generated.map Name.toString) ==
      (← ofExcept <| expectedRow.getObjVal? "generated")
    unless binding == (← ofExcept <| expectedRow.getObjVal? "binding") &&
        inventory == (← ofExcept <| expectedRow.getObjVal? "generated_declarations") do
      IO.FS.writeFile (output ++ ".mismatch.json") ((Json.mkObj [
        ("binding", binding), ("generated", toJson (generated.map Name.toString)),
        ("generated_declarations", inventory),
        ("expected", expectedRow)]).pretty ++ "\n")
      throwError "independent_binding_generated_mismatch:{target}"
    let sealed ← serializeSealArtifact (SealRecords.forRoot assessed target)
    unless sealed == (← ofExcept <| expectedRow.getObjValAs? String "seal_bytes") do
      throwError "independent_seal_mismatch:{target}"
    return Json.mkObj [
      ("target", toJson target.toString), ("direct_imports", toJson #[target.toString]),
      ("module_count", toJson sourceCount), ("only_target_import_closure", toJson true),
      ("source_extension_evaluation", toJson false),
      ("report_direct_imports", toJson
        #[target.toString, "LeanInformationAuditRegTests.ContractIndependent"]),
      ("report_module_count", toJson reportModules.size),
      ("fixed_judge_closure_count", toJson judgeModules.size),
      ("only_target_and_fixed_judge_report_closure", toJson true),
      ("raw_generated_order_equal", toJson rawOrderEqual),
      ("generated_declaration_inventory_equal", toJson true),
      ("binding_generated_seal_equal", toJson true)]
  setEnv driver
  IO.FS.writeFile output (reading.pretty ++ "\n")
  logInfo m!"[PASS] contract_independent_environment:{target}"

end LeanInformationAuditRegTests.ContractIndependent
