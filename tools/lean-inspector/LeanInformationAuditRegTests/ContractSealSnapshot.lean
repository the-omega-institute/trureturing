import LeanInformationAuditRegTests.ContractAssertions
import LeanInformationAuditRegTests.ContractSealFixtures.Reg.Catalogs.PointwiseDisequality.SealedCatalog
import Reg.Catalogs.PointwiseDisequalityRegistrations
import LeanInformationAudit.Contract.Discovery
import LeanInformationAudit.SealCommand

namespace LeanInformationAuditRegTests.ContractSealSnapshot
open Lean Meta Elab Command LeanInformationAudit LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

private def oldRoot : Name := `Reg.Catalogs.PointwiseDisequalityRegistrations
private def typedRoot : Name :=
  `LeanInformationAuditRegTests.ContractSealFixtures.Reg.Catalogs.PointwiseDisequality.SealedCatalog

private def occurrenceJson (row : LeanInformationAudit.ExpectedOccurrence) : Json := Json.mkObj [
  ("rootId", toJson row.rootId.toString),
  ("theoremName", toJson row.theoremName.toString),
  ("objectArenaName", toJson row.objectArenaName.toString),
  ("statementIdentity", toJson row.statementIdentity),
  ("registrationModuleName", toJson row.registrationModuleName.toString),
  ("capturedStatement", toJson (row.capturedStatement.map reprStr))]

/-- Each layout uses its own compiler import closure and the production snapshot
validator, assessment and kernel seal publisher. Serialized names are retained. -/
private unsafe def layout (typed : Bool) : IO Json := do
  enableInitializersExecution
  let root := if typed then typedRoot else oldRoot
  let search ← searchPathRef.get
  let artifacts := (← Repository.root) / ".lake/build/lean-inspector/reg/lib/lean"
  let env ← try
    searchPathRef.set (artifacts :: search)
    importModules #[{ module := root }, { module := `LeanInformationAudit.SealCommand },
      { module := `LeanInformationAudit.Contract.Discovery }] {} (trustLevel := 0) (loadExts := true)
  finally searchPathRef.set search
  let action : MetaM Json := do
    let (contract, sealInput) ← if typed then do
      let requirements ← RootStructure.requiredFor #[root] Discovery.moduleSource
      let snapshot ← Discovery.discoverWithStructure requirements #[root]
      unless snapshot.roots.size == 1 && snapshot.seals.size == 1 do
        throwError "control:typed_catalog_seal_cardinality"
      let contract := snapshot.roots[0]!.2
      RootCatalogs.acquireProvenance contract
      liftCommandElabM <| RootCatalogs.declare contract
      let some (_, sealInput) := snapshot.seals[0]?
        | throwError "control:typed_seal_missing"
      pure (contract, sealInput)
    else do
      let some contract := RootCatalogs.find? (← getEnv) root
        | throwError "control:recorded_catalog_missing"
      let some (_, sealInput) := (SealInputs.owned (← getEnv)).find? (·.2.rootId == root)
        | throwError "control:recorded_seal_missing"
      pure (contract, sealInput)
    unless contract.rootId == root && sealInput.rootId == root do
      throwError "control:root_identity"
    replayRegistrationInputs (← RegistrationAssessmentInput.capture root)
    liftCommandElabM <| validateRegistrySnapshot root (← getEnv)
    let expected := expectedOccurrencesForRoot (← getEnv) root
    withOptions (fun _ => sealInput.options) <| GeneratedDeclarations.withOwner root do
      assessAndSealRegistration (← RegistrationAssessmentInput.capture root)
    let records := SealRecords.forRoot (← getEnv) root
    unless records.size == 1 do throwError "control:seal_record_count:{records.size}"
    let artifact ← serializeSealArtifact records
    let artifact ← match Json.parse artifact with
      | .ok value => pure value | .error error => throwError "control:seal_json:{error}"
    return Json.mkObj [
      ("rootId", toJson root.toString),
      ("expected", toJson (expected.map occurrenceJson)),
      ("source", toJson ((snapshotExpectations root contract.source).map occurrenceJson)),
      ("baseline", toJson ((snapshotExpectations root contract.baseline).map occurrenceJson)),
      ("seal", artifact), ("seal_records", toJson records.size),
      ("snapshot_validated", toJson true)]
  let ((value, _), _) ← action.run.toIO
    { fileName := "<seal snapshot control>", fileMap := default,
      options := (({} : Options).set `maxRecDepth (100000 : Nat)).set
        `maxHeartbeats (2000000 : Nat) }
    { env := env.setExporting false }
  return value

run_meta do
  let recorded ← layout false
  let typed ← layout true
  assertTest "seal.snapshot.recorded_validated"
    ((recorded.getObjValAs? Bool "snapshot_validated").toOption == some true)
  assertTest "seal.snapshot.typed_validated"
    ((typed.getObjValAs? Bool "snapshot_validated").toOption == some true)
  logInfo m!"SEAL_SNAPSHOT_CONTROL {(Json.mkObj [("recorded", recorded), ("typed", typed)]).compress}"

end LeanInformationAuditRegTests.ContractSealSnapshot
