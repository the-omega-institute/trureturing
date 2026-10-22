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
  for i in [:12] do
    let goal ← mkFreshExprMVar (mkConst ``True)
    let entry : DiskLookup.Entry := {
      module := "checkpoint-fixture", name := s!"attempt-{i}", parts := #[(s!"attempt-{i}",0)]}
    let trace ← boundedLookupCandidate table entry goal.mvarId! do
      if i == 11 then
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
