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
        sealRecord.compiledEvidence && sealRecord.catalog.units.size == 2) do
      throw <| IO.userError "compiled.seal:complete_unit_membership"
    let snapshot ← ArtifactAssessment.discover store root
    let some (inputOwner, row) := snapshot.registrations[0]?
      | throw <| IO.userError "compiled.coverage:registration_missing"
    let coverageFields ← IO.ofExcept <| Contract.Literal.fields (store.constants[·]?)
      ``Contract.NodeCoverage row.input.coverage 2
    let omitted := mkApp2 (mkConst ``Contract.NodeCoverage.mk)
      (mkApp (mkConst ``List.nil [.zero]) (mkConst ``Contract.NodeCoordinate)) coverageFields[1]!
    let rejectedAction : ArtifactRegistration.M (Array BindingRecord) := do
      ArtifactRegistration.register inputOwner { row with input := { row.input with coverage := omitted } }
      ArtifactRegistration.assessJoined root
    let (rejected, _) ← rejectedAction.run { store, plans := state.plans }
    unless rejected.size == 1 && rejected.all (fun record => match record.result with
        | .declaredUnresolved message => (message.splitOn "E7.registration_coverage").length == 2
        | _ => false) do
      throw <| IO.userError "compiled.coverage:invalid_root_not_unresolved"
    IO.println "[PASS] invalid raw coverage produces an unresolved record without admission"
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
    IO.println "[PASS] compiled seal: complete real catalog membership and snapshot rejections"
    let sharedRoot := `Reg.Catalogs.SharedInformationRoot.SealedCatalog
    RawArtifacts.loadModule sharedRoot reader
    let (_, sharedSeals) ← ArtifactAssessment.assess (← reader.get) sharedRoot
    let own := sharedSeals.filter (·.catalog.rootId == sharedRoot)
    unless own.size == 12 && own.all (·.compiledEvidence) &&
        own.foldl (fun count row => count + row.catalog.units.size) 0 == 13 do
      throw <| IO.userError "compiled.seal:shared_unit_membership"
    IO.println "[PASS] compiled shared seal: 12 catalogs and 13 exact imported units"
  finally searchPathRef.set saved

end LeanInformationAuditRegTests.CompiledSeal
