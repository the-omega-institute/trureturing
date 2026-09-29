import LeanInformationAudit.Tests.Projection.BoundedProjection

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit
open LeanInformationAudit.Tests.Projection.Bounded

/-- info: bounded independent bottom: zero search branches -/
#guard_msgs in
run_cmd do
  let (selected, work) ← liftTermElabM do
    canonicalSelectionWork (← mkConstWithFreshMVarLevels ``catalog)
      #[``aFirst, ``bSecond, ``cThird] #[0, 1, 2]
  unless selected == #[0, 1, 2] do throwError "independent bottom representative"
  unless work == 0 do throwError "bounded independent bottom searched {work} branches"
  logInfo "bounded independent bottom: zero search branches"
