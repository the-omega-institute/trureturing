import LeanInformationAudit.Census.Report

open Lean LeanInformationAudit DispositionCensus

run_cmd do
  let wire := "sha256:" ++ String.ofList (List.replicate 64 '0')
  let node := Json.mkObj [("freeze_status", toJson "frozen"),
    ("declarations", toJson #[Json.mkObj [("kind", toJson "theorem"),
      ("declaration_name_key", toJson "ns(n0,2:é)"), ("statement_id", toJson wire)]])]
  let fields ← ofExcept truthExportIdentity.getObj?
  let json := Json.mkObj (fields.toArray.toList ++
    [("source_commit", toJson "head"), ("nodes", toJson #[node])])
  for bytes in [json.compress, json.pretty ++ "\n"] do
    let expected ← ofExcept <| parseReportData bytes
    let actual ← parseReportDataIO bytes
    unless actual.headSha == expected.headSha && actual.reportSha256 == expected.reportSha256 &&
        (toJson actual.theorems).compress == (toJson expected.theorems).compress do
      throwError "reportNativeHashBinding: IO parser changed bytes, membership or identity"
  let rejected ← try
    discard <| parseReportDataIO "{}"
    pure false
  catch _ => pure true
  unless rejected do throwError "reportNativeHashBinding: malformed report accepted"
