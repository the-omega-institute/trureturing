import LeanInformationAudit.Census.Query
import LeanInformationAudit.Tests.Census.Evidence

open Lean Meta Elab Command LeanInformationAudit DispositionCensus
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.Query

theorem malformedTarget : 8 + 1 = 9 := by decide

def malformedEvidence : UnreachableElaborationEvidence (8 + 1 = 9) where
  reason := .noCanonicalObjectCarrier
  candidateArena := none
  explanation := "Deliberately missing the required failed obligation."

run_cmd liftTermElabM do
  let index ← CensusQuery.indexScope `LeanInformationAudit.Tests.Census.Evidence
  let unreachable ← CensusQuery.assess index "fixture-head" ⟨``Evidence.closedNumerical, "sha256:000000000000000000000000000000000000000000000000000000000000002d"⟩
  match unreachable with
  | .certified (.unreachable value) =>
    unless value.evidence == ``Evidence.noCarrier do throwError "directUnreachableWitness: wrong witness"
  | _ => throwError "directUnreachableWitness: complete direct evidence was downgraded"
  let bounded ← CensusQuery.assess index "fixture-head" ⟨``Evidence.boundedTheorem, "sha256:0000000000000000000000000000000000000000000000000000000000000013"⟩
  match bounded with
  | .certified (.boundedFiniteTruncation value) =>
    unless value.truncationFamily == ``Evidence.truncation && value.bound == 12 &&
        value.comparisonStatement == ``Evidence.comparison do
      throwError "directBoundedWitness: wrong family or comparison"
  | _ => throwError "directBoundedWitness: complete direct evidence was downgraded"
  let malformed ← CensusQuery.indexScope (← getEnv).header.mainModule
  let mut rejected := false
  try
    discard <| CensusQuery.assess malformed "fixture-head" ⟨``malformedTarget, "sha256:0000000000000000000000000000000000000000000000000000000000000044"⟩
  catch error =>
    unless (← error.toMessageData.toString).contains "evidence.failed_obligation" do throw error
    rejected := true
  unless rejected do throwError "malformedDirectEvidenceRejected: invalid evidence became an observation"
  logInfo "directUnreachableWitness directBoundedWitness malformedDirectEvidenceRejected"

end LeanInformationAudit.Tests.Census.Query
