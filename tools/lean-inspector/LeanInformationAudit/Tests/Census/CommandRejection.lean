import LeanInformationAudit.Tests.Census.Evidence
import LeanInformationAudit.Tests.Census.Coverage

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command

namespace LeanInformationAudit.Tests.Census

/-- Exercise successful publication and inspect its count and kernel certificate. -/
def expectAcceptedCensus (root inventoryName certificate : Name)
    (inventory : DispositionInventory) (structuralCount : Nat) : CommandElabM Unit :=
  IO.FS.withTempDir fun dir => do
    let bytes := (Json.mkObj [
      ("schema", toJson "stratalint.truth-export"), ("schema_version", toJson (1 : Nat)),
      ("dialect", toJson "stratalint.truth-export.v1"),
      ("producer", toJson "TruthExportCommand"), ("source_commit", toJson inventory.headSha),
      ("nodes", Json.arr #[Json.mkObj [("declarations", Json.arr <|
        inventory.entries.map fun row => Json.mkObj [
          ("kind", toJson "theorem"),
          ("declaration_name_key", toJson (encodeNameKey row.1.theoremName)),
          ("statement_id", toJson row.1.statementId)])]])]).compress
    let reportPath := dir / "report.json"
    let outputPath := dir / "census.json"
    IO.FS.writeFile reportPath bytes
    let input := Syntax.mkStrLit reportPath.toString
    let destination := Syntax.mkStrLit outputPath.toString
    let head := Syntax.mkStrLit inventory.headSha
    let digest := Syntax.mkStrLit ("sha256:" ++ Sha256.hex bytes.toUTF8)
    let rootId := mkIdent root
    let inventoryId := mkIdent inventoryName
    let certificateId := mkIdent certificate
    elabCommand (← `(command|
      #disposition_census root $rootId report $input head $head report_sha256 $digest
        inventory $inventoryId certificate $certificateId output $destination))
    let projection ← ofExcept <| Json.parse (← IO.FS.readFile outputPath)
    let counts ← ofExcept <| projection.getObjVal? "counts"
    unless (← ofExcept <| counts.getObjValAs? Nat "structural_occurrence") == structuralCount do
      throwError "unexpected structural count: {counts.compress}"
    let sources ← ofExcept <| projection.getObjValAs? (Array Json) "source_inputs"
    let env ← getEnv
    let expectedModules := inventory.entries.toList.filterMap fun row =>
      if row.2.className == "structural_occurrence" then
        some (((env.getModuleIdxFor? row.1.theoremName).map
          (env.header.moduleNames[·.toNat]!)).getD env.header.mainModule).toString
      else none
    let modules ← sources.toList.mapM fun (source : Json) =>
      Lean.ofExcept <| source.getObjValAs? String "module"
    unless modules == expectedModules.eraseDups.mergeSort (· < ·) do
      throwError "incorrect structural source input closure"
    for source in sources do
      let path ← ofExcept <| source.getObjValAs? String "path"
      let digest ← ofExcept <| source.getObjValAs? String "sha256"
      unless digest == "sha256:" ++ Sha256.hex (← IO.FS.readBinFile path) do
        throwError "incorrect structural source hash"
    liftTermElabM do
      let name := (← getCurrNamespace) ++ certificate
      Lean.Meta.checkWithKernel (← Lean.Meta.mkConstWithFreshMVarLevels name)
      unless (← Lean.collectAxioms name).all
          (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
        throwError "unexpected coverage axioms"
    logInfo m!"accepted=true structural={structuralCount} certificate-kernel-checked=true"

/-- Check the public command's diagnostic and both publication boundaries. -/
def expectRejectedCensus (root inventoryName certificate : Name)
    (inventory : DispositionInventory) (expected : String) : CommandElabM Unit :=
  IO.FS.withTempDir fun dir => do
    let bytes := (Json.mkObj [
      ("schema", toJson "stratalint.truth-export"), ("schema_version", toJson (1 : Nat)),
      ("dialect", toJson "stratalint.truth-export.v1"),
      ("producer", toJson "TruthExportCommand"), ("source_commit", toJson inventory.headSha),
      ("nodes", Json.arr #[Json.mkObj [("declarations", Json.arr <|
        inventory.entries.map fun row => Json.mkObj [
          ("kind", toJson "theorem"),
          ("declaration_name_key", toJson (encodeNameKey row.1.theoremName)),
          ("statement_id", toJson row.1.statementId)])]])]).compress
    let reportPath := dir / "report.json"
    let outputPath := dir / "census.json"
    IO.FS.writeFile reportPath bytes
    let input := Syntax.mkStrLit reportPath.toString
    let destination := Syntax.mkStrLit outputPath.toString
    let head := Syntax.mkStrLit inventory.headSha
    let digest := Syntax.mkStrLit ("sha256:" ++ Sha256.hex bytes.toUTF8)
    let rootId := mkIdent root
    let inventoryId := mkIdent inventoryName
    let certificateId := mkIdent certificate
    let before ← get
    elabCommand (← `(command|
      #disposition_census root $rootId report $input head $head report_sha256 $digest
        inventory $inventoryId certificate $certificateId output $destination))
    let messages := (← get).messages.toList.drop before.messages.toList.length
    let errors := messages.filter (·.severity == .error)
    let rejected := errors.length == 1 && (← errors.allM fun message => do
      pure ((← message.data.toString) == expected))
    modify fun state => { state with messages := before.messages }
    let outputAbsent := !(← outputPath.pathExists)
    let certificateName := (← getCurrNamespace) ++ certificate
    let certificateAbsent := !(← getEnv).contains certificateName
    unless outputAbsent do
      let projection ← ofExcept <| Json.parse (← IO.FS.readFile outputPath)
      let counts ← ofExcept <| projection.getObjVal? "counts"
      logInfo m!"accepted-output counts={counts.compress}"
    unless certificateAbsent do
      liftTermElabM do
        Lean.Meta.checkWithKernel (← Lean.Meta.mkConstWithFreshMVarLevels certificateName)
        let axioms ← Lean.collectAxioms certificateName
        unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
          throwError "unexpected coverage axioms: {axioms}"
        logInfo m!"accepted-certificate kernel-checked=true axioms={axioms}"
    unless rejected && outputAbsent && certificateAbsent do
      throwError "rejected={rejected} output-absent={outputAbsent} \
        certificate-absent={certificateAbsent} diagnostics={← errors.mapM (·.data.toString)}"
    logInfo expected
    logInfo "rejected=true output-absent=true certificate-absent=true"

end LeanInformationAudit.Tests.Census
