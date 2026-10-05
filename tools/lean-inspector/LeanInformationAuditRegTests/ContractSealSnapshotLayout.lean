import LeanInformationAuditRegTests.ContractControl
import LeanInformationAudit.Contract.Discovery
import LeanInformationAudit.SealCommand

namespace LeanInformationAuditRegTests.ContractSealSnapshotLayout
open Lean Meta Elab Command LeanInformationAudit LeanInformationAudit.Contract

private def occurrenceJson (row : LeanInformationAudit.ExpectedOccurrence) : Json := Json.mkObj [
  ("rootId", toJson row.rootId.toString),
  ("theoremName", toJson row.theoremName.toString),
  ("objectArenaName", toJson row.objectArenaName.toString),
  ("statementIdentity", toJson row.statementIdentity),
  ("registrationModuleName", toJson row.registrationModuleName.toString),
  ("capturedStatement", toJson (row.capturedStatement.map reprStr))]

/-- Assess and seal one layout in its compiler import environment. -/
def snapshot (root : Name) : MetaM Json := do
  let reachable := reachableModules (moduleImports (← getEnv)) root
  let owners := ((← getEnv).header.moduleNames.filter fun owner =>
    reachable.contains owner && (`Reg).isPrefixOf owner).filter (· != root) |>.push root
  let requirements ← RootStructure.requiredFor owners Discovery.moduleSource
  let snapshot ← Discovery.discoverWithStructure requirements owners
  unless snapshot.roots.size == 1 && snapshot.seals.size == 1 do
    throwError "control:typed_catalog_seal_cardinality"
  let contract := snapshot.roots[0]!.2
  let some (_, sealInput) := snapshot.seals[0]?
    | throwError "control:typed_seal_missing"
  TypedAssessment.assessSnapshot snapshot
  unless contract.rootId == root && sealInput.rootId == root do
    throwError "control:root_identity"
  liftCommandElabM <| validateRegistrySnapshot root (← getEnv)
  let expected := expectedOccurrencesForRoot (← getEnv) root
  withOptions (fun _ => sealInput.options) <| GeneratedDeclarations.withOwner root do
    assessAndSealRegistration (← RegistrationAssessmentInput.capture root) sealInput
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

end LeanInformationAuditRegTests.ContractSealSnapshotLayout
