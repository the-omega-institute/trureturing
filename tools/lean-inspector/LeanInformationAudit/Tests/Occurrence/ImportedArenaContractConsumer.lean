import LeanInformationAudit.Tests.Occurrence.ImportedArenaContract
import LeanInformationAudit.Tests.SourceIsolation

open Lean Elab Command LeanInformationAudit ImportedContractProbe ImportedContractFixture

-- Native imports must transport evidence for rows that were never registered.
run_cmd do
  for (name, owner) in #[( ``expectedAlias, ``arena), (``expectedCopy, ``expectedCopy),
      (``sourceAlias, ``arena), (``sourceCopy, ``sourceCopy),
      (``baselineAlias, ``arena), (``baselineCopy, ``baselineCopy)] do
    unless (← liftTermElabM <| resolveCanonicalArenaNameFromEvidence name) == owner do
      throwError "native contract import lost evidence: {name}"
  let some contract := RootCatalogs.find? (← getEnv) contributor
    | throwError "native contract import lost independent input"
  RootCatalogs.declare { contract with rootId := (← getEnv).header.mainModule }

run_cmd do
  for name in #[``expectedGroupedAlias, ``expectedGroupedCopy,
      ``sourceGroupedAlias, ``sourceGroupedCopy, ``baselineGroupedAlias, ``baselineGroupedCopy] do
    let diagnostic ← liftTermElabM do
      try return s!"accepted owner={← resolveCanonicalArenaNameFromEvidence name}"
      catch ex => ex.toMessageData.toString
    unless diagnostic == s!"IE-C003 ArenaSourceUnsupported arena={name} owner={name}" do
      throwError "[FAIL] grouped contract native evidence {name}: {diagnostic}"
  logInfo "[PASS] Q3 contract inputs retain dual rejection after native import"

/-- error: IE-C003 ArenaSourceUnavailable declaration=ImportedContractProbe.missingEvidence reason=provenance -/
#guard_msgs (error) in
run_cmd do
  discard <| liftTermElabM <| resolveCanonicalArenaNameFromEvidence ``missingEvidence

-- Remove only private fixture source bytes after compilation acquisition. The
-- actual audited seal must succeed using the native evidence and original Expr.
run_cmd LeanInformationAudit.Tests.withPrivateSources do
  let path ← ArenaProvenance.moduleSource
    `LeanInformationAudit.Tests.Occurrence.ImportedArenaContractSource
  liftIO <| IO.FS.removeFile path
  elabCommand (← `(command| #seal_information_theory))
  let env ← getEnv
  unless (SealRecords.occurrencesForRoot env env.header.mainModule).size == 2 do
    throwError "source-free seal did not publish both occurrences"
  logInfo "native contract provenance sealed with source absent; two occurrences"
