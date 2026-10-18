import LeanInformationAuditRegTests.SearchReduction.Calibration

/-! Resource faults and missing inputs never certify finite-search failure. -/
open Lean Meta
open LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction

run_meta do
  let env ← getEnv
  let normal ← attempt env [] (mkConst ``True) "fixture/normal-exhaustion" (fun _ => pure false)
  unless normal.outcome == .exhausted do throwError "normal exhaustion was misclassified"
  let before ← IO.getNumHeartbeats
  let limited ← attempt env [] (mkConst ``True) "fixture/heartbeat" fun _ => do
    IO.addHeartbeats (budget * 1000 + 1)
    checkSystem "reference-search-heartbeat-fixture"
    return false
  IO.setNumHeartbeats before
  unless limited.outcome == .incomplete .heartbeat do throwError "heartbeat was not preserved"
  let broken ← attempt env [] (mkConst ``True) "fixture/execution" fun _ => do
    throwError "fixture implementation error"
  unless broken.outcome == .incomplete .execution do throwError "error was counted as exhaustion"

#search_reduction ReferenceSearchMissing.target
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline []
  using [] as missingResult
#guard missingResult = Verdict.insufficient
#guard missingResult.baseline = Run.incomplete Failure.missing

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.content
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [LeanInformationAudit.Tests.SearchReduction.Candidates.answer] as aliasLeakResult
#guard aliasLeakResult = Verdict.insufficient
#guard aliasLeakResult.paired = Run.incomplete Failure.isolation

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.content
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [LeanInformationAudit.Tests.SearchReduction.Candidates.disguisedAnswer] as packedLeakResult
#guard packedLeakResult = Verdict.insufficient
#guard packedLeakResult.paired = Run.incomplete Failure.isolation

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.content
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as emptyStructureResult
#guard emptyStructureResult = Verdict.insufficient
#guard emptyStructureResult.baseline = Run.exhausted
#guard emptyStructureResult.paired = Run.incomplete Failure.missing

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.hiddenTarget
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [] as hiddenDependencyResult
#guard hiddenDependencyResult = Verdict.insufficient
#guard hiddenDependencyResult.baseline = Run.incomplete Failure.isolation

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.content
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [LeanInformationAudit.Tests.SearchReduction.Candidates.iffAnswer] as iffLeakResult
#guard iffLeakResult = Verdict.insufficient
#guard iffLeakResult.paired = Run.incomplete Failure.isolation
