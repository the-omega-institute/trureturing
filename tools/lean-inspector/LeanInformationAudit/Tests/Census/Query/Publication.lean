import LeanInformationAudit.Census.Publish
import LeanInformationAudit.Tests.Census.Evidence

open Lean LeanInformationAudit DispositionCensus CensusProjection

run_cmd do
  let full := Tests.Census.Evidence.inventory
  let selected := { full with entries := full.entries.extract 0 1 }
  let report : FrozenReport :=
    { headSha := full.headSha, reportSha256 := "original-export", theorems := full.entries.map (·.1) }
  let summary := Json.mkObj (summaryFields report selected #[])
  unless (summary.getObjValAs? Nat "requested_keys").toOption == some 4 &&
      (summary.getObjValAs? String "status").toOption == some "partial" &&
      (summary.getObjValAs? Bool "certified_complete").toOption == some false &&
      (summary.getObjValAs? Nat "coverage_theorem_count").toOption == some 1 do
    throwError "partialCertifiedDenominator: 1/4 certified cannot be certified_complete"
  let bytes := Json.mkObj [("nodes", Json.arr <| full.entries.mapIdx fun index row =>
    Json.mkObj [("freeze_status", toJson "frozen"),
      ("repo_path", toJson (if index == 0 then "Selected.lean" else "Other.lean")),
      ("declarations", Json.arr #[Json.mkObj [("kind", toJson "theorem"),
        ("statement_id", toJson row.1.statementId)]])])]
  let selectedReport ← ofExcept <| selectReport report bytes.compress "Selected"
  unless selectedReport.reportSha256 == report.reportSha256 && selectedReport.theorems.size == 1 do
    throwError "partialExportIdentity: original export identity lost"
  match checkCoverage report.headSha selectedReport.theorems selected with
  | .error error => throwError error
  | .ok () => pure ()
  logInfo "partialCertifiedDenominator partialExportIdentity"
