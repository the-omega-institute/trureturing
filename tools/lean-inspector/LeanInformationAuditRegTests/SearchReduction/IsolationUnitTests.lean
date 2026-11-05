import LeanInformationAuditRegAnalysis.SearchReduction.Isolation
import LeanInformationAuditRegTests.SearchReduction.Candidates
import LeanInformationAuditRegTests.SearchReduction.GraphCandidates

/-! Actual production unit boundaries and reconstruction-domain invariance.
Heartbeat injection here tests the execution boundary, not production negative
calibration coverage. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction
set_option Elab.async false
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let initial ← IO.getNumHeartbeats
  let phase ← IO.mkRef "not-started"
  isolationRejection.set none
  isolationUnitReadings.set #[]
  -- Prior units cannot consume this unit's fixed allocation.
  IO.addHeartbeats (3 * reconstructionBudget * 1000)
  for source in #[`first, `second] do
    discard <| withRestatementUnit `target source phase do
      IO.addHeartbeats (reconstructionBudget * 1000 / 2)
      checkSystem "isolation-unit-test/independent"
  let rows ← isolationUnitReadings.get
  unless rows.size == 2 && rows.all (fun row =>
      (row.getObjValAs? String "status").toOption == some "complete") do
    throwError "earlier units consumed a later check allocation"
  -- Recursive work shares one allocation; the second half must overflow.
  let fault ← catchLookupCandidate
    (do
      discard <| withRestatementUnit `target `overLimit phase do
        IO.addHeartbeats (reconstructionBudget * 1000 / 2)
        checkSystem "isolation-unit-test/first-half"
        IO.addHeartbeats (reconstructionBudget * 1000 / 2 + 1000000)
        checkSystem "isolation-unit-test/second-half"
      pure none)
    (fun ex => return some (← isolationFailure ex true (← phase.get)))
  IO.setNumHeartbeats initial
  let some (failure, reason) := fault | throwError "unit overrun was accepted"
  unless failure == .heartbeat &&
      (reason.splitOn "restatement-unit:target:overLimit:single-source-and-legacy").length > 1 &&
      (reason.splitOn "arm=paired").length > 1 do
    throwError "unit overrun lost its named isolation fault: {reason}"
  let rows ← isolationUnitReadings.get
  unless rows.size == 3 &&
      (rows[2]!.getObjValAs? String "status").toOption == some "incomplete:unit-heartbeat" do
    throwError "unit overrun reading was lost"
  logInfo s!"ISOLATION_UNIT_REGRESSION independent=true recursive_shared=true \
    disposition=incomplete reason={reason}"

set_option maxHeartbeats 0 in
run_cmd do
  enableInitializersExecution
  let source ← getEnv
  let base ← importModules #[{module := `Mathlib.Tactic}] {} 0
    (leakEnv := false) (loadExts := true)
  let a := ``Candidates.addition
  let b := ``GraphCandidates.squareFact
  let variants := #[#[a, b], #[b, a], #[a, b, a, b]]
  let mut reference : Option (Array Json) := none
  for additions in variants do
    isolationUnitReadings.set #[]
    isolationUnitCount.set 0
    isolationRejection.set none
    let request : Request := {
      target := ``Candidates.doubledContent, additions,
      «baseline» := #[], baselineCommit := "b02b98342945a1a724a227db4fa38e376640e573"}
    let result ← prepare source base request true
    if let .error (_, reason) := result then
      throwError "invariance preparation failed: {reason}"
    let rows ← isolationUnitReadings.get
    let canonical ← rows.mapM fun row => do
      let target ← IO.ofExcept (row.getObjValAs? String "target")
      let source ← IO.ofExcept (row.getObjValAs? String "source")
      let status ← IO.ofExcept (row.getObjValAs? String "status")
      pure (Json.mkObj [("target", toJson target), ("source", toJson source), ("status", toJson status)])
    if let some expected := reference then
      unless (toJson canonical).compress == (toJson expected).compress do
        throwError "S order or duplicates changed a single check conclusion"
    else reference := some canonical
    logInfo s!"ISOLATION_S_INVARIANCE {Json.mkObj [
      ("S", toJson (additions.map Name.toString)), ("m", toJson (← isolationUnitCount.get)),
      ("checks", toJson canonical), ("prepared", toJson true)] |>.compress}"
