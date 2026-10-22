import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.LookupBaseline

/-! Implication stays in B_T while exact membership can certify an external
B0 statement. Both checks use the original candidate module identity. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
set_option Elab.async false
set_option maxHeartbeats 0

run_cmd do
  enableInitializersExecution
  let base ← importModules #[{module := `Lean}] {} 0
    (leakEnv := false) (loadExts := true)
  let index ← DiskLookup.openIndex "build/lean-inspector/lookup-index/lookup-fixture"
    "lookup-fixture" "56a005855ea17e0b0958f73ec801ae140b0a1679"
  liftTermElabM do
    let source ← getEnv
    let type ← Term.elabType
      (← `(LeanInformationAudit.Tests.SearchReduction.LookupBaseline.Mark 9))
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    let calls ← IO.mkRef 0
    let table : LookupTable := {
      environment := base, disk? := some index
      load? := some fun _ _ _ => do
        calls.modify (· + 1)
        throwError "external implication loader was invoked"}
    withEnv base do
      let type ← copyStatement source .anonymous type
      let result ← localRebuild type [] (some table)
      unless result.cost == .one && result.lookup.complete &&
          result.lookup.unloaded == 0 && (← calls.get) == 0 do
        throwError "B_T exclusion failed: {result.detail}"
      emitLookupRecord "LOOKUP_SCOPE implication_external_loads=0 nohit=true"
    enableInitializersExecution
    let fixtureBase ← importModules
      #[{module := `LeanInformationAuditRegTests.SearchReduction.LookupBaseline}] {} 0
      (leakEnv := false) (loadExts := true)
    withEnv fixtureBase do
      let result ← localRebuild type [] (some {
        environment := fixtureBase, disk? := some index, implicationModules? := some #[]})
      unless result.cost == .one && result.lookup.complete do
        throwError "incidental imports enlarged the explicit B_T scope"
      emitLookupRecord "LOOKUP_SCOPE incidental_imports_excluded=true"
    let table ← onDemandLookup {environment := base, disk? := some index}
    let type ← Term.elabType
      (← `(∀ renamed : Nat,
        LeanInformationAudit.Tests.SearchReduction.LookupBaseline.Mark renamed ∧
        LeanInformationAudit.Tests.SearchReduction.LookupBaseline.Side))
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    withEnv base do
      let type ← copyStatement source .anonymous type
      let result ← localRebuild type [] (some table)
      unless result.cost == .zero && result.proof?.isSome &&
          result.lookup.source? ==
            some ``LeanInformationAudit.Tests.SearchReduction.LookupBaseline.pair do
        throwError "external B0 membership was lost: {result.detail}"
      unless result.lookup.unloaded == 1 do
        throwError "membership did not isolate its one external candidate"
      checkLocalProof type result.proof?.get!
      emitLookupRecord "LOOKUP_SCOPE membership_B0=true external_candidates=1 kernel=true std3=true"
