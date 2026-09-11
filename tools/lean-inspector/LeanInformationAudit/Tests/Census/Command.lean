import LeanInformationAudit.Tests.Census.Evidence
import LeanInformationAudit.Tests.Census.Coverage

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command

namespace LeanInformationAudit.Tests.Census.Command

def inputBytes : String := (Json.mkObj [
  ("schema", toJson "stratalint.truth-export"),
  ("schema_version", toJson (2 : Nat)),
  ("dialect", toJson "stratalint.truth-export.v2"),
  ("producer", toJson "TruthExportCommand"),
  ("source_commit", toJson Evidence.inventory.headSha),
  ("nodes", Json.arr #[Json.mkObj [("freeze_status", toJson "frozen"),
    ("declarations", Json.arr <|
    Evidence.inventory.entries.map fun entry => Json.mkObj [
      ("kind", toJson "theorem"),
      ("declaration_name_key", toJson (encodeNameKey entry.1.theoremName)),
      ("statement_id", toJson entry.1.statementId)])],
    Json.mkObj [("freeze_status", toJson "proven-not-yet-frozen"),
      ("declarations", Json.arr #[Json.mkObj [
        ("kind", toJson "theorem"),
        ("declaration_name_key", toJson (encodeNameKey `Fixture.pending)),
        ("statement_id", toJson "sha256:000000000000000000000000000000000000000000000000000000000000001f")]])]])]).compress

/-- info: Except.ok 4 -/
#guard_msgs in
#eval (parseReport "fixture-head" ("sha256:" ++ Sha256.hex inputBytes.toUTF8) inputBytes).map
  (·.theorems.size)

run_cmd IO.FS.withTempDir fun dir => do
  let reportPath := dir / "report.json"
  let firstPath := dir / "census.json"
  let repeatPath := dir / "repeat.json"
  let reportStx := Syntax.mkStrLit reportPath.toString
  let firstStx := Syntax.mkStrLit firstPath.toString
  let repeatStx := Syntax.mkStrLit repeatPath.toString
  IO.FS.writeFile reportPath inputBytes
  let digest := Syntax.mkStrLit ("sha256:" ++ Sha256.hex inputBytes.toUTF8)
  elabCommand (← `(command|
    #disposition_census root LeanInformationAudit.Tests.Census.Evidence
      report $reportStx
      head "fixture-head" report_sha256 $digest
      inventory LeanInformationAudit.Tests.Census.Evidence.inventory
      certificate censusCoverage output $firstStx))
  elabCommand (← `(command|
    #disposition_census root LeanInformationAudit.Tests.Census.Evidence
      report $reportStx
      head "fixture-head" report_sha256 $digest
      inventory LeanInformationAudit.Tests.Census.Evidence.inventory
      certificate censusCoverageRepeat output $repeatStx))
  unless (← IO.FS.readFile firstPath) == (← IO.FS.readFile repeatPath) do
    throwError "census output is not byte-identical"
  let projection ← ofExcept <| Json.parse (← IO.FS.readFile firstPath)
  unless (← ofExcept <| projection.getObjValAs? Nat "theorem_count") == 4 do
    throwError "non-frozen theorem was counted"
  let rows ← ofExcept <| projection.getObjValAs? (Array Json) "rows"
  unless rows.size == 4 && rows.all (fun row =>
      row.getObjValAs? String "statement_id" != .ok "sha256:000000000000000000000000000000000000000000000000000000000000001f") do
    throwError "non-frozen theorem was published"
  let counts ← ofExcept <| projection.getObjVal? "counts"
  unless (← ofExcept <| counts.getObjValAs? Nat "structural_occurrence") == 1 do
    throwError "generated parity theorem was not counted"

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
