import LeanInformationAudit.Tests.Census.Evidence
import LeanInformationAudit.Tests.Census.Coverage

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command

namespace LeanInformationAudit.Tests.Census.Command

def inputBytes : String := (Json.mkObj [
  ("schema", toJson "stratalint.truth-export"),
  ("schema_version", toJson (1 : Nat)),
  ("dialect", toJson "stratalint.truth-export.v1"),
  ("producer", toJson "TruthExportCommand"),
  ("source_commit", toJson Evidence.inventory.headSha),
  ("nodes", Json.arr #[Json.mkObj [("declarations", Json.arr <|
    Evidence.inventory.entries.map fun entry => Json.mkObj [
      ("kind", toJson "theorem"),
      ("declaration_name_key", toJson (encodeNameKey entry.1.theoremName)),
      ("statement_id", toJson entry.1.statementId)])]])]).compress

run_cmd do
  IO.FS.writeFile "/tmp/lean-information-census-command-report.json" inputBytes
  let digest := Syntax.mkStrLit ("sha256:" ++ Sha256.hex inputBytes.toUTF8)
  elabCommand (← `(command|
    #disposition_census root LeanInformationAudit.Tests.SealSuccess
      report "/tmp/lean-information-census-command-report.json"
      head "fixture-head" report_sha256 $digest
      inventory LeanInformationAudit.Tests.Census.Evidence.inventory
      certificate censusCoverage output "/tmp/lean-information-census-command.json"))
  elabCommand (← `(command|
    #disposition_census root LeanInformationAudit.Tests.SealSuccess
      report "/tmp/lean-information-census-command-report.json"
      head "fixture-head" report_sha256 $digest
      inventory LeanInformationAudit.Tests.Census.Evidence.inventory
      certificate censusCoverageRepeat output "/tmp/lean-information-census-command-repeat.json"))
  unless (← IO.FS.readFile "/tmp/lean-information-census-command.json") ==
      (← IO.FS.readFile "/tmp/lean-information-census-command-repeat.json") do
    throwError "census output is not byte-identical"

#print axioms censusCoverage
#print axioms censusCoverageRepeat

/-- info: Except.error "IE-C044 DispositionCensusMismatch head=fixture-head component=theorem_count expected=4 actual=5" -/
#guard_msgs in
#eval do
  let report : FrozenReport :=
    ⟨Evidence.inventory.headSha, "digest", Evidence.inventory.keys.toArray⟩
  let projection ← artifact report Evidence.inventory
  let modified := projection.setObjVal! "theorem_count" (toJson (5 : Nat))
  checkArtifact report Evidence.inventory modified

/-- info: Except.error "IE-C044 DispositionCensusMismatch head=fixture-head component=rows expected=[] actual=[1]" -/
#guard_msgs in
#eval do
  let emptyInventory : DispositionInventory := ⟨"fixture-head", #[]⟩
  let report : FrozenReport := ⟨"fixture-head", "digest", #[]⟩
  let projection ← artifact report emptyInventory
  let modified := projection.setObjVal! "rows" (toJson [1])
  checkArtifact report emptyInventory modified

end LeanInformationAudit.Tests.Census.Command
