import LeanInformationAudit.DispositionCensus
import D5.S3.ConceptDynamics.InformationEscape.InformationRoot

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit DispositionCensus
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.LandedFinite

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- All eleven landed finite occurrences have the required evidence. The IDs here
belong to a synthetic fixture report; production IDs must come from truth-export. -/
run_cmd do
  let registrations := InformationRegistry.entries (← getEnv)
  unless registrations.size == 11 do throwError "expected eleven landed occurrences"
  let mut rows : Array (Sigma fun key : StatementKey => AnalysisDisposition key) := #[]
  for (registration, i) in registrations.toList.zipIdx do
    let proofName := (← getCurrNamespace) ++ registration.arenaName.str "nondegenerate"
    liftTermElabM do
      let arenaExpr ← mkAppM ``PrimitiveLawArena.toArena
        #[← mkConstWithFreshMVarLevels registration.arenaName]
      let proposition ← mkAppM ``Arena.Nondegenerate #[arenaExpr]
      let proof ← mkDecideProof proposition
      addDecl <| .thmDecl { name := proofName, levelParams := [], type := proposition, value := proof }
    elabCommand (← `(command| #print axioms $(mkIdent proofName)))
    rows := rows.push ⟨⟨registration.theoremName, s!"fixture-statement-id-{i}"⟩,
      .finiteOccurrence ⟨registration.canonicalObjectArenaName, registration.unitName,
        registration.realizationName, proofName, registration.arenaName.str "__state_enumeration"⟩⟩
  let inventory : DispositionInventory := ⟨"fixture-head", rows⟩
  liftTermElabM do
    validateEvidence frozenInformationRootId inventory
    let report : FrozenReport := ⟨"fixture-head", "fixture-report", inventory.keys.toArray⟩
    let proof ← coverageProof report inventory
    addDecl <| .thmDecl {
      name := `LeanInformationAudit.Tests.Census.LandedFinite.exactCoverage
      levelParams := []
      type := ← inferType proof
      value := proof }
  unless (count inventory).finiteOccurrence == 11 do throwError "finite count mismatch"

#print axioms exactCoverage

end LeanInformationAudit.Tests.Census.LandedFinite
