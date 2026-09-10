import LeanInformationAudit.Census.Manifest
import LeanInformationAudit.Tests.Census.Manifest.ReportIO

open Lean LeanInformationAudit DispositionCensus CensusManifest

private def zeroId := "sha256:" ++ String.ofList (List.replicate 64 '0')
private def oneId := "sha256:" ++ String.ofList (List.replicate 63 '0') ++ "1"

run_cmd do
  let keys : Array StatementKey := #[⟨`T, zeroId⟩, ⟨`U, oneId⟩]
  let report : FrozenReport := ⟨"head", "digest", keys⟩
  let manifest : CensusKeyManifest := ⟨"head", "digest", `Root, [0, 1]⟩
  let duplicates : Array StatementKey := #[⟨`T, zeroId⟩, ⟨`Other, zeroId⟩]
  let check (label expected : String) (result : Except String Unit) := do
    match result with
    | .error error => unless error.contains expected do throwError "{label}: {error}"
    | .ok _ => throwError "{label}: invalid input accepted"
  check "reportDuplicatePrecedence" "IE-C044" <| checkManifestBinding
    { report with theorems := duplicates } `Root duplicates
    { manifest with headSha := "stale", reportSha256 := "wrong" } []
  check "inventoryDuplicatePrecedence" "IE-C035" <| checkManifestBinding
    report `Root duplicates { manifest with headSha := "stale", reportSha256 := "wrong" } []
  check "digestBeforeMissing" "component=report_sha256" <| checkManifestBinding
    report `Root #[] { manifest with reportSha256 := "wrong" } []
  check "headBeforeMissing" "component=head" <| checkManifestBinding
    report `Root #[] { manifest with headSha := "stale" } []
  check "missingAfterIdentity" "IE-C034" <| checkManifestBinding
    report `Root #[] { manifest with keys := [] } manifest.keys
  check "reportMalformedBeforeHead" "IE-C044" <|
    (parseReport "wrong" "wrong" truthExportIdentity.compress).map (fun _ => ())
  for value in [0, 1, 2 ^ 256 - 1] do
    let wire ← ofExcept <| renderStatementId value
    unless decodeStatementId `Boundary wire == .ok value do throwError "codecBoundaryRoundTrip"
  if (renderStatementId (2 ^ 256)).isOk then throwError "codecBoundedNat"

-- Mixed faults: these assertions fail against fd4c31cafb with IE-C036 and
-- IE-C034 respectively. Keep identity and absence as distinct phases.
run_cmd do
  let bad := "sha256:" ++ String.ofList (List.replicate 63 '0')
  let rows : Array StatementKey := #[⟨`T, zeroId⟩, ⟨`U, zeroId⟩]
  let frozen : Array StatementKey := #[⟨`T, bad⟩]
  for result in [checkKeyCoverage "head" frozen "head" rows,
      checkManifestBinding ⟨"head", "digest", frozen⟩ `Root rows
        ⟨"head", "digest", `Root, [0, 0]⟩ [0]] do
    match result with
    | .error error => unless error.startsWith "IE-C035" do
        throwError "inventoryDuplicateBeforeMalformedReport: {error}"
    | .ok _ => throwError "inventoryDuplicateBeforeMalformedReport: accepted"

run_cmd do
  let rows : Array StatementKey := #[⟨`T, zeroId⟩]
  let report : FrozenReport := ⟨"head", "digest", rows.push ⟨`U, oneId⟩⟩
  let manifest : CensusKeyManifest := ⟨"head", "digest", `Root, [1]⟩
  match checkManifestBinding report `Root rows manifest [0, 1] with
  | .error error => unless error.contains "component=statement_id_nat" do
      throwError "manifestNatBeforeMissingRow: {error}"
  | .ok _ => throwError "manifestNatBeforeMissingRow: accepted"
