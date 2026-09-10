import LeanInformationAudit.Census.Query
import LeanInformationAudit.Tests.Census.Evidence

open Lean Meta Elab Command LeanInformationAudit DispositionCensus
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.Query

theorem privateTarget : 11 + 1 = 12 := by decide
theorem privateObligation : ClosedNumericalObligation ``privateTarget (11 + 1) 12 := ⟨privateTarget⟩
private def privateWitness : UnreachableElaborationEvidence (11 + 1 = 12) where
  reason := .noCanonicalObjectCarrier
  candidateArena := none
  explanation := "Private named witness in the declared scope."
  failedObligation := some ``privateObligation

theorem aliasTarget : 13 + 1 = 14 := by decide
theorem aliasObligation : ClosedNumericalObligation ``aliasTarget (13 + 1) 14 := ⟨aliasTarget⟩
abbrev AliasedEvidence := UnreachableElaborationEvidence (13 + 1 = 14)
def aliasedWitness : AliasedEvidence where
  reason := .noCanonicalObjectCarrier
  candidateArena := none
  explanation := "Transparent alias outside the syntactic type-head domain."
  failedObligation := some ``aliasObligation

run_cmd liftTermElabM do
  let index ← CensusQuery.indexScope (← getEnv).header.mainModule
  let privateRow ← CensusQuery.assess index "fixture-head" ⟨``privateTarget, "sha256:0000000000000000000000000000000000000000000000000000000000000043"⟩
  match privateRow with
  | .certified (.unreachable value) =>
    unless value.evidence == ``privateWitness do throwError "privateDeclarationIncluded: wrong witness"
  | _ => throwError "privateDeclarationIncluded: private named evidence was excluded"
  let aliasKey : StatementKey := ⟨``aliasTarget, "sha256:0000000000000000000000000000000000000000000000000000000000000011"⟩
  validateEvidence index.root ⟨"fixture-head", #[⟨aliasKey,
    .certified (.unreachable ⟨.noCanonicalObjectCarrier, ``aliasedWitness⟩)⟩]⟩
  let aliasRow ← CensusQuery.assess index "fixture-head" aliasKey
  unless aliasRow.className == "observed" do
    throwError "transparentAliasBoundary: update the documented syntactic-domain limitation"
  logInfo "privateDeclarationIncluded transparentAliasBoundary (normalization deferred to J4)"

end LeanInformationAudit.Tests.Census.Query
