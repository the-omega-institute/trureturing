import LeanInformationAuditRegTests.ProductionInputs
import LeanInformationAudit.Census.Query
import Reg.Catalogs.InformationRoot
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit DispositionCensus
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.LandedFinite

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- All eleven landed finite occurrences have the required evidence. The IDs here
belong to a synthetic fixture report; production IDs must come from truth-export. -/
run_cmd do
  let expected := Reg.Support.InformationRootContract.contract.expected
  unless expected.size == 11 do throwError "expected eleven independent landed occurrences"
  let registrations ← liftCoreM <| LeanInformationAuditRegTests.productionEntries expected
  unless registrations.size == 11 do throwError "expected eleven landed occurrences"
  for registration in registrations do
    let proofName := (← getCurrNamespace) ++ registration.arenaName.str "nondegenerate"
    liftTermElabM do
      let arenaExpr := (← RegistrationElaboration.normalizeArena
        (← mkConstWithFreshMVarLevels registration.arenaName)).finite
      let proposition ← mkAppM ``Arena.Nondegenerate #[arenaExpr]
      let proof ← mkDecideProof proposition
      addDecl <| .thmDecl { name := proofName, levelParams := [], type := proposition, value := proof }
    elabCommand (← `(command| #print axioms $(mkIdent proofName)))
  let index ← liftTermElabM <| CensusQuery.indexScope (← getEnv).header.mainModule
  let mut rows : Array (Sigma fun key : StatementKey => CensusAssessment key) := #[]
  for (registration, i) in registrations.toList.zipIdx do
    let key : StatementKey := ⟨registration.theoremName, ← ofExcept <| renderStatementId i⟩
    -- The consumer normalizes the arena and discovers typed certificates;
    -- migrated registrations need not use the old generated-name convention.
    let assessment ← liftTermElabM <| CensusQuery.assess index "fixture-head" key
    let .certified (.finiteOccurrence payload) := assessment
      | throwError "landed occurrence was not certified: {registration.theoremName}"
    unless payload.canonicalArena == registration.canonicalObjectArenaName &&
        payload.registration == registration.unitName &&
        payload.realization == registration.realizationName do
      throwError "landed occurrence identity mismatch: {registration.theoremName}"
    rows := rows.push ⟨key, assessment⟩
  let inventory : DispositionInventory := ⟨"fixture-head", rows⟩
  liftTermElabM do
    validateEvidence (← getEnv).header.mainModule inventory
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
