import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.FaultPaths
import LeanInformationAuditRegTests.SearchReduction.PresentationCoverage
import LeanInformationAuditRegTests.SearchReduction.SingleSourceTests
import LeanInformationAuditRegTests.SearchReduction.RawOriginsTests
import LeanInformationAuditRegTests.SearchReduction.Candidates
import LeanInformationAuditRegTests.SearchReduction.PresentationCandidates

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

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.contentPair
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [LeanInformationAudit.Tests.SearchReduction.Candidates.answer] as targetPackingLeakResult
#guard targetPackingLeakResult = Verdict.insufficient
#guard targetPackingLeakResult.paired = Run.incomplete Failure.isolation

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.content
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [LeanInformationAudit.Tests.SearchReduction.Candidates.splitTarget] as nonneutralPackLeakResult
#guard nonneutralPackLeakResult = Verdict.insufficient
#guard nonneutralPackLeakResult.paired = Run.incomplete Failure.isolation

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.content
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [LeanInformationAudit.Tests.SearchReduction.Candidates.shiftedAnswer] as closureLeakResult
#guard closureLeakResult = Verdict.insufficient
#guard closureLeakResult.paired = Run.incomplete Failure.isolation

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.splitTarget
  at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline]
  using [LeanInformationAudit.Tests.SearchReduction.Candidates.answer,
    LeanInformationAudit.Tests.SearchReduction.Candidates.shiftedAnswer] as splitStructureLeakResult
#guard splitStructureLeakResult = Verdict.insufficient
#guard splitStructureLeakResult.paired = Run.incomplete Failure.isolation

#search_reduction LeanInformationAudit.Tests.SearchReduction.Candidates.doubledContent
  at "a5e5b163319079eeb1b4b431395c65e43beb4b07"
  baseline [LeanInformationAuditRegTests.SearchReduction.Baseline,
    LeanInformationAuditRegTests.SearchReduction.PresentationBaseline]
  using [LeanInformationAudit.Tests.SearchReduction.PresentationCandidates.arithmetic]
    as baselinePresentationStructureResult
#guard baselinePresentationStructureResult = Verdict.insufficient
#guard baselinePresentationStructureResult.paired = Run.incomplete Failure.isolation

run_meta do
  let getType := fun n => do pure (← getConstInfo n).type
  let answer ← getType ``LeanInformationAudit.Tests.SearchReduction.Candidates.answer
  let changed ← getType ``LeanInformationAudit.Tests.SearchReduction.Candidates.changedPremise
  if ← certifiedRestatement answer changed then
    throwError "presentation erased a premise from the full telescope"
  if ← certifiedRestatement changed answer then
    throwError "presentation erased a premise in the reverse direction"

run_meta do
  let source := (← getConstInfo
    ``LeanInformationAudit.Tests.SearchReduction.Baseline.commuted).type
  forallTelescopeReducing source fun xs body => do
    for direction in #[← mkArrow body.appFn!.appArg! body.appArg!,
        ← mkArrow body.appArg! body.appFn!.appArg!] do
      let target ← mkForallFVars xs direction
      unless ← certifiedRestatement target source do
        throwError "presentation failed to preserve a full-telescope Iff direction"
  let answer := (← getConstInfo
    ``LeanInformationAudit.Tests.SearchReduction.Candidates.answer).type
  let .forallE name domain body _ := answer | throwError "fixture telescope missing"
  let implicit := Expr.forallE name domain body .implicit
  if ← certifiedRestatement answer implicit then
    throwError "presentation erased BinderInfo"

run_meta do
  let saved ← saveState
  let goal ← mkFreshExprMVar (mkConst ``True)
  let target := mkIdent `ReferenceSearchMissing.target
  let owner := mkIdent `LeanInformationAuditRegTests.SearchReduction.Candidates
  let rejected ← try
    discard <| (Elab.Term.withoutErrToSorry <| Elab.Tactic.run goal.mvarId!
      (Elab.Tactic.evalTactic (← `(tactic|
        fail_if_success (reference_baseline $target
          at "b530df86e6e9c4709edecd3009bb96c3d4ebc8be" baseline []
          from [$owner]))))).run'
    pure false
  catch ex =>
    let message ← ex.toMessageData.toString
    unless message.startsWith "The tactic provided to `fail_if_success` succeeded" do throw ex
    pure true
  saved.restore
  unless rejected do throwError "outer negative guard accepted an incomplete replay"
