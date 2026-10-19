import LeanInformationAuditRegAnalysis.SearchReduction.Runner

/-! A resource fault inside an actual leaf tactic must survive both exception
handlers and the assembled search outcome. Ordinary failure stays exhausted. -/
open Lean Meta
open LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction

run_meta do
  let env ← getEnv
  let before ← IO.getNumHeartbeats
  let hint ← `(tactic| run_tac do
    IO.addHeartbeats (LeanInformationAudit.SearchReduction.budget * 1000 + 1)
    Lean.Core.checkSystem "reference-search-leaf-heartbeat-fixture")
  let (outcome, rows) ← search env [] (mkConst ``False) #[] #[(0, hint)]
  IO.setNumHeartbeats before
  unless outcome == .incomplete .heartbeat do
    throwError "leaf heartbeat was converted into normal exhaustion: {reprStr outcome}"
  unless rows.any (fun row => row.strategy.startsWith "leaf[0]/" &&
      row.outcome == .incomplete .heartbeat) do
    throwError "leaf heartbeat observation missing"
  let (outcome, _) ← search env [] (mkConst ``False) #[] #[(0, ← `(tactic| fail))]
  IO.setNumHeartbeats before
  unless outcome == .exhausted do
    throwError "ordinary leaf failure was not normal exhaustion"
