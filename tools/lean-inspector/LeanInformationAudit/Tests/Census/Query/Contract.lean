import LeanInformationAudit.Census.Query
import LeanInformationAudit.Tests.Census.Evidence
import LeanInformationAudit.Tests.Census.Query.Registration

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit DispositionCensus

namespace LeanInformationAudit.Tests.Census.Query

set_option maxRecDepth 100000
set_option maxHeartbeats 0

run_cmd liftTermElabM do
  let key : StatementKey := ⟨``target, "sha256:000000000000000000000000000000000000000000000000000000000000002a"⟩
  let mut missingScopeRejected := false
  try
    let _ ← CensusQuery.indexScope `MissingCensusModule
  catch error =>
    unless (← error.toMessageData.toString).contains "existing-module" do throw error
    missingScopeRejected := true
  unless missingScopeRejected do throwError "missingScopeRejected: query error became an observation"
  let outside ← CensusQuery.indexScope `LeanInformationAudit.Tests.Census.Query.Source
  let row ← CensusQuery.assess outside "fixture-head" key
  match row with
  | .observed value =>
    unless value.queryCompleted && value.importScope.completed && value.candidates.isEmpty &&
        value.importScope.modules.contains `LeanInformationAudit.Tests.Census.Query.Source &&
        !value.importScope.modules.contains `LeanInformationAudit.Tests.Census.Query.Registration do
      throwError "outsideScopeObserved: registration leaked across the declared scope"
  | .certified _ => throwError "outsideScopeObserved: outside registration certified"
  let included ← CensusQuery.indexScope `LeanInformationAudit.Tests.Census.Query.Registration
  let registeredRow ← CensusQuery.assess included "fixture-head" key
  unless included.finite.any (fun entry => entry.theoremName == key.theoremName &&
      entry.registrationModuleName == `LeanInformationAudit.Tests.Census.Query.Registration) do
    throwError "registrationScopeIncluded: in-scope registration was not enumerated"
  match registeredRow with
  | .observed value =>
    unless value.queryCompleted && value.importScope.completed &&
        value.candidates.contains ``target.__information_unit &&
        value.candidates.contains ``legacy &&
        value.importScope.modules.contains `LeanInformationAudit.Tests.Census.Query.Registration do
      throwError "registrationScopeIncluded: in-scope candidates were not returned"
  | .certified _ => throwError "registrationScopeIncluded: unsealed registration certified"
  let inside ← CensusQuery.indexScope `LeanInformationAudit.Tests.Census.Evidence
  let finiteKey : StatementKey := ⟨``SealSuccess.idTheorem, "sha256:0000000000000000000000000000000000000000000000000000000000000015"⟩
  let row ← CensusQuery.assess inside "fixture-head" finiteKey
  unless row.className == "finite_occurrence" do
    throwError "insideScopeCertified: certifying registration was not selected"
  validateEvidence `LeanInformationAudit.Tests.Census.Evidence
    ⟨"fixture-head", #[⟨finiteKey, row⟩]⟩
  let structuralKey : StatementKey := ⟨``Evidence.structuralTheorem, "sha256:0000000000000000000000000000000000000000000000000000000000000029"⟩
  let structuralRow ← CensusQuery.assess inside "fixture-head" structuralKey
  unless structuralRow.className == "structural_occurrence" do
    throwError "structuralRegistryCertified: imported provenance registry was not queried"
  let mut rejected := false
  try
    let _ ← CensusQuery.assess outside "fixture-head" ⟨`MissingTheorem, "sha256:0000000000000000000000000000000000000000000000000000000000000042"⟩
  catch _ => rejected := true
  unless rejected do throwError "missingTheoremRejected: query error became an observation"
  logInfo "missingScopeRejected outsideScopeObserved insideScopeCertified structuralRegistryCertified missingTheoremRejected"

end LeanInformationAudit.Tests.Census.Query
