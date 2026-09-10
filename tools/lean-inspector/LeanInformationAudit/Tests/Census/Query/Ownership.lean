import LeanInformationAudit.Census.Command
import LeanInformationAudit.Tests.Census.Query.OwnerFirst
import LeanInformationAudit.Tests.Census.Query.OwnerSecond

open Lean Lean.Elab.Command LeanInformationAudit

run_cmd liftTermElabM do
  let env <- getEnv
  let owner := `LeanInformationAudit.Tests.Census.Query.OwnerSecond
  let name := `LeanInformationAudit.Tests.Census.Query.ownerParent.congr_simp
  let index <- CensusQuery.indexScope env.header.mainModule
  unless CensusQuery.owningModule env name != owner do
    throwError "ownerMembershipPositive: fixture did not exercise first-import ambiguity"
  unless <- CensusOwnership.recordedModuleContainsTheorem env index.modules owner name do
    throwError "ownerMembershipPositive: valid realizing module rejected"
  let key := StatementKey.mk name ("sha256:" ++ String.ofList (List.replicate 64 '0'))
  let row <- CensusQuery.assess index "fixture-head" key (some owner)
  let .observed value := row | throwError "ownerMembershipPositive: expected observation"
  unless value.owningModule == owner do
    throwError "ownerMembershipPositive: recorded provenance was lost"
  let scope := DispositionCensus.censusRootModules env owner
  if scope.contains (CensusQuery.owningModule env name) then
    throwError "ownerMembershipScopedPositive: first importer was not excluded"
  unless <- CensusOwnership.theoremInScope env scope name do
    throwError "ownerMembershipScopedPositive: valid occurrence outside first-import scope rejected"
  DispositionCensus.validateEvidence owner ⟨"fixture-head", #[⟨key, .observed
    { value with root := owner, importScope := ⟨scope, true⟩ }⟩]⟩
  if <- CensusOwnership.recordedModuleContainsTheorem env #[] owner name then
    throwError "ownerMembershipOutOfScope: out-of-scope module accepted"
  if <- CensusOwnership.recordedModuleContainsTheorem env index.modules `Init name then
    throwError "ownerMembershipAbsent: declaration absent from module constants accepted"
  let some moduleIndex := env.getModuleIdx? owner | throwError "missing fixture module"
  let data := env.header.moduleData[moduleIndex.toNat]!
  let .thmInfo info <- getConstInfo name | throwError "fixture is not a theorem"
  let wrongType := ConstantInfo.thmInfo { info with type := mkConst ``False }
  let wrongLevels := ConstantInfo.thmInfo { info with levelParams := [`u] }
  for (label, candidate) in [("ownerMembershipDifferentType", wrongType),
      ("ownerMembershipDifferentLevels", wrongLevels)] do
    if CensusOwnership.moduleContainsTheorem data candidate then
      throwError "{label}: mismatching declaration accepted"
  let parent <- getConstInfo `LeanInformationAudit.Tests.Census.Query.ownerParent
  let some parentIndex := env.getModuleIdx? `LeanInformationAudit.Tests.Census.Query.OwnerSource
    | throwError "ownerMembershipWrongKind: missing definition module"
  let parentData := env.header.moduleData[parentIndex.toNat]!
  unless parentData.constNames.contains parent.name do
    throwError "ownerMembershipWrongKind: definition absent from the control module"
  if CensusOwnership.moduleContainsTheorem parentData parent then
    throwError "ownerMembershipWrongKind: definition accepted as theorem"
