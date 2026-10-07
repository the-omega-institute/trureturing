import Reg.Catalogs.PointwiseDisequalityRegistrations.SealedCatalog
import Reg.Catalogs.SharedInformationRoot.SealedCatalog
import LeanInformationAudit.ArtifactAssessment

namespace LeanInformationAuditRegTests.CompiledSeal
open Lean LeanInformationAudit

unsafe def check (reader : IO.Ref RawArtifacts.Store) : IO Unit := do
  let fixturePath ← Repository.source ".lake/build/lean-inspector/reg/lib/lean"
  let saved ← searchPathRef.get
  searchPathRef.set (fixturePath :: saved)
  try
    let root := `Reg.Catalogs.PointwiseDisequalityRegistrations.SealedCatalog
    RawArtifacts.loadModule root reader
    RawArtifacts.loadModule `LeanInformationAudit.TemplateEnrollment reader
    let store ← reader.get
    let (state, seals) ← ArtifactAssessment.assess store root
    unless seals.size == 1 && seals.all (fun sealRecord =>
        sealRecord.compiledEvidence && sealRecord.stateCard == 4 &&
        sealRecord.offDiagonalPairCount == 12 && sealRecord.fullEscapeCount == 0 &&
        sealRecord.theorems.size == 2 && sealRecord.theorems.all (fun row =>
          row.uniqueCaptureCount == 2 && row.withoutEscapeCount == 2 &&
          row.primitiveCount > 0 && row.primitiveAxes.size == row.primitiveCount &&
          row.primitiveKernelAddress.startsWith "sha256:" &&
          row.roleSignatureHistogram.foldl (fun sum bin => sum + bin.2) 0 == 2)) do
      throw <| IO.userError "compiled.seal:complete_counts_roles_and_primitives"
    let snapshot ← ArtifactAssessment.discover store root
    let some (_, contract) := snapshot.roots.find? (·.2.rootId == root)
      | throw <| IO.userError "compiled.seal:root_missing"
    let entries := ArtifactRegistration.entriesFor state root
    let missing := { contract with expected := contract.expected.extract 1 contract.expected.size }
    let result := CompiledSnapshots.registry (state.store.constants[·]?) root (some missing) entries
    unless (match result with
        | .error reason => (reason.splitOn "component=member-set").length == 2
        | .ok _ => false) do
      throw <| IO.userError "compiled.seal:missing_member_accepted"
    let some first := contract.source[0]?
      | throw <| IO.userError "compiled.seal:source_missing"
    let baseline := { contract with baseline := #[{ first with registrationModuleName := `otherContributor }] }
    let result := CompiledSnapshots.registry (state.store.constants[·]?) root (some baseline) entries
    unless (match result with
        | .error reason => (reason.splitOn "component=frozen-baseline-contributor-modules").length == 2
        | .ok _ => false) do
      throw <| IO.userError "compiled.seal:baseline_contributor_accepted"
    IO.println "[PASS] compiled seal: complete real catalog, row counts, roles, primitive statistics and snapshot rejections"
    let sharedRoot := `Reg.Catalogs.SharedInformationRoot.SealedCatalog
    RawArtifacts.loadModule sharedRoot reader
    let (_, sharedSeals) ← ArtifactAssessment.assess (← reader.get) sharedRoot
    let own := sharedSeals.filter (·.catalog.rootId == sharedRoot)
    unless own.size == 12 && own.all (·.compiledEvidence) &&
        own.foldl (fun count row => count + row.theorems.size) 0 == 13 do
      throw <| IO.userError "compiled.seal:shared_literal_conclusions"
    IO.println "[PASS] compiled shared seal: 12 catalogs and 13 rows with reused conclusion proofs"
  finally searchPathRef.set saved

end LeanInformationAuditRegTests.CompiledSeal
