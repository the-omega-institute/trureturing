import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.LookupBaseline

/-! Recall, nonrecursive closure and incomplete-basis regression checks. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction.LookupBaseline
set_option Elab.async false
set_option maxHeartbeats 0

run_cmd do
  enableInitializersExecution
  let base ← importModules #[{module := `Lean}] {} 0 (loadExts := true)
  liftTermElabM do
    let source ← getEnv
    let index ← DiskLookup.openFixtureIndex
      "build/lean-inspector/search-reduction-test-index/lookup-fixture" "lookup-fixture"
      "56a005855ea17e0b0958f73ec801ae140b0a1679"
    let table ← onDemandLookup {environment := base, disk? := some index}
    let positive ← Term.elabType (← `(∀ n : Nat, Mark n ∧ Side))
    let negative ← Term.elabType (← `(Mark 9))
    Term.synthesizeSyntheticMVarsNoPostponing
    for (type, expected) in #[(← instantiateMVars positive, EdgeCost.zero),
        (← instantiateMVars negative, EdgeCost.one)] do
      withEnv base do
        let type ← copyStatement source .anonymous type
        for _ in [:2] do
          let result ← localRebuild type [] (some table)
          unless result.cost == expected do
            throwError "cold candidate certification: {result.detail}"
          if expected == .one then
            unless result.lookup.complete && result.lookup.unloaded == 0 do
              throwError "external implication was loaded or exclusion became incomplete"
          logInfo s!"LOOKUP_COLD cost={reprStr result.cost} {result.detail}"
