import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.LookupBaseline

/-! Exact per-attempt checkpoint replay, including a kernel-checked hit,
normal failures, and an unknown residual across fresh compiler processes. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
set_option Elab.async false
set_option maxHeartbeats 0

run_cmd liftTermElabM do
  let budget ← IO.mkRef ({} : LookupBudgetState)
  let table : LookupTable := {environment := ← getEnv, budget? := some budget}
  let mut rows := #[]
  for i in [:72] do
    let goal ← mkFreshExprMVar (mkConst ``True)
    let entry : DiskLookup.Entry := {
      module := "checkpoint-fixture", name := s!"attempt-{i}", parts := #[(s!"attempt-{i}",0)]}
    let trace ← boundedLookupCandidate table entry goal.mvarId! do
      if i == 71 then
        goal.mvarId!.assign (mkConst ``True.intro)
        return {complete := true, source? := some ``True.intro, attempted := 1}
      else if i == 5 then
        return {complete := false, missing := #[entry.leanName], failures := #["fixture-unknown"]}
      else return {complete := true, attempted := 1}
    rows := rows.push (Json.mkObj [
      ("complete", toJson trace.complete), ("source", toJson (trace.source?.map Name.toString)),
      ("attempted", toJson trace.attempted), ("failures", toJson trace.failures),
      ("missing", toJson (trace.missing.map Name.toString))])
  emitLookupRecord s!"LOOKUP_RESUME_SEMANTICS {(Json.arr rows).compress}"

run_cmd do
  enableInitializersExecution
  let base ← importModules #[{module := `Lean}] {} 0 (leakEnv := false) (loadExts := true)
  liftTermElabM do
    let source ← getEnv
    let index ← DiskLookup.openFixtureIndex "build/lean-inspector/search-reduction-test-index/lookup-fixture"
      "lookup-fixture" "56a005855ea17e0b0958f73ec801ae140b0a1679"
    let table ← onDemandLookup {environment := base, disk? := some index}
    let type ← Term.elabType (← `(∀ n : Nat,
      LeanInformationAudit.Tests.SearchReduction.LookupBaseline.Mark n ∧
      LeanInformationAudit.Tests.SearchReduction.LookupBaseline.Side))
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    let bytes ← withEnv base do
      let type ← copyStatement source .anonymous type
      let graph : ProofGraph := {
        root := 0, vertices := [{id := 0, type}], edges := [{conclusion := 0}], complete := true}
      let reading ← evaluateGraph graph (some table)
      let baselineProof? ← assembleZero reading.graph
      let pairedProof? ← assembleZero reading.graph true
      let reading := {reading with
        baselineProof?, pairedProof?, isolated := true, structureChecked := true, structureClean := true, presentationComplete := true}
      unless reading.baseline == ⟨.finite 0, .finite 0⟩ && reading.baselineProof?.isSome do
        throwError "resume fixture did not certify its actual lookup graph"
      let observation : Observation := {
        target := `checkpointProjection, graph? := some reading,
        verdict := classifyGraph reading, base := reading.baselineProbe.outcome,
        paired := reading.pairedProbe.outcome}
      return (observationJson observation).compress
    emitLookupRecord s!"LOOKUP_RESUME_GRAPH {bytes}"

run_cmd liftTermElabM do
  withLetDecl `checkpointLocal (mkConst ``True) (mkConst ``True.intro) fun value => do
    let goal ← mkFreshExprMVar (mkConst ``True)
    let table : LookupTable := {environment := ← getEnv}
    let entry : DiskLookup.Entry := {module := "checkpoint-fixture", name := "let-hit", parts := #[("let-hit",0)]}
    let trace ← boundedLookupCandidate table entry goal.mvarId! do
      goal.mvarId!.assign value
      return {complete := true, source? := some ``True.intro, attempted := 1}
    unless trace.complete && trace.source?.isSome && (← goal.mvarId!.isAssigned) do
      throwError "let-bound checkpoint lost its checked proof"
    emitLookupRecord s!"LOOKUP_RESUME_LET {Json.mkObj [
      ("complete", toJson trace.complete), ("source", toJson (trace.source?.map Name.toString)),
      ("assigned", toJson (← goal.mvarId!.isAssigned))] |>.compress}"
