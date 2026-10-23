import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.LookupBaseline

/-! Recall, nonrecursive closure and incomplete-basis regression checks. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction.LookupBaseline
set_option Elab.async false
set_option maxHeartbeats 0

run_cmd liftTermElabM do
  let timeout : MetaM LocalResult := do
    IO.addHeartbeats (localBudget * 1000 + 1)
    checkSystem "lookup.isolation.fixture"
    return {cost := .one}
  let exhausted : MetaM LocalResult := pure {cost := .one, detail := "exhausted"}
  let success : MetaM LocalResult := do
    let type := mkConst ``True
    let proof := mkConst ``True.intro
    checkLocalProof type proof
    return {cost := .zero, proof? := some proof, detail := "certified"}
  let recovered ← independentRebuild timeout success
  unless recovered.cost == .zero && recovered.proof?.isSome do
    throwError "local timeout escaped to successful lookup: {recovered.detail}"
  let preserved ← independentRebuild success timeout
  unless preserved.cost == .zero do throwError "lookup timeout erased local success"
  let unknown ← independentRebuild exhausted timeout
  unless unknown.cost == .unknown do throwError "lookup timeout became NoHit"
  let both ← independentRebuild timeout timeout
  unless both.cost == .unknown do throwError "two timeouts became NoHit"
  let negative ← independentRebuild exhausted exhausted
  unless negative.cost == .one do throwError "normal exhaustion became unknown"
  let cancelled ← boundedRebuildBranch (throwInterruptException : MetaM LocalResult)
  unless cancelled.cost == .unknown && cancelled.detail == "cancelled" do
    throwError "interrupt escaped branch boundary"
  logInfo s!"LOOKUP_BRANCH_ISOLATION local_timeout_lookup_success=zero local_success=zero lookup_timeout={reprStr unknown.cost} both_timeout={reprStr both.cost} both_exhausted=one interrupt=unknown budget={localBudget}"

run_cmd liftTermElabM do
  let source ← getEnv
  let result ← boundedRebuildBranch do
    IO.addHeartbeats (localBudget * 1000 + 1)
    discard <| copyCertificateExpression {source, enclosingBudget := true} (mkConst ``True.intro)
    return {cost := .one}
  unless result.cost == .unknown && result.detail == "heartbeat" do
    throwError "candidate vocabulary copy escaped the enclosing allocation"
  logInfo "LOOKUP_COPY_BUDGET enclosing=true timeout=unknown"

run_cmd liftTermElabM do
  let directory : System.FilePath := "build/lean-inspector/lookup-index/colliding-owner-fixture"
  IO.FS.createDirAll directory
  let type := mkConst ``True
  let keys ← DiscrTree.mkPath type
  let entry : DiskLookup.Entry := {
    module := "FirstOwner", name := "sameConstant", parts := #[("sameConstant", 0)]}
  let other := {entry with module := "SecondOwner"}
  let tree : DiscrTree DiskLookup.Entry := ({} : DiscrTree DiskLookup.Entry)
    |>.insertKeyValue keys entry |>.insertKeyValue keys other
  pickle (directory / "owners.pickle") ({tree} : DiskLookup.PickledShard)
  let header : DiskLookup.Header := {
    basis := "owners", mathlib := "fixture", inputs := 0, storage := "", root := "",
    digest := 0, complete := true, modules := 2, declarations := 2, indexed := 2, missing := #[]}
  let index : DiskLookup.Index := {
    directory, header, manifest := #[(hash (keys[0]!), #["owners.pickle"])]}
  let found ← DiskLookup.queryMature index type
  unless found.complete && found.entries.size == 2 &&
      found.entries[0]!.module != found.entries[1]!.module do
    throwError "distinct compiled owners were collapsed by constant name"
  logInfo "LOOKUP_COLLIDING_OWNERS retained=true"

run_cmd liftTermElabM do
  let budget ← IO.mkRef ({} : LookupBudgetState)
  let prepared ← boundedRebuildBranch (do
    withLookupPreparation (some budget) do
      IO.addHeartbeats (localBudget * 1000 + 1)
    checkSystem "lookup.search_after_preparation"
    return {cost := .one}) (some budget)
  unless prepared.cost == .one && (← budget.get).preparation > localBudget * 1000 do
    throwError "preparation was charged to search"
  let exceeded ← boundedRebuildBranch (do
    withLookupPreparation (some budget) do
      IO.addHeartbeats (lookupPreparationBudget * 1000 + 1)
      checkSystem "lookup.preparation_overflow"
    return {cost := .one}) (some budget)
  unless exceeded.cost == .unknown && exceeded.detail == "preparation-heartbeat" do
    throwError "preparation overflow became NoHit or escaped its branch: {exceeded.detail}"
  logInfo "LOOKUP_SPLIT_BUDGET preparation_excluded=true preparation_overflow=unknown"

run_cmd liftTermElabM do
  let budget ← IO.mkRef ({} : LookupBudgetState)
  let table : LookupTable := {environment := ← getEnv, budget? := some budget}
  let goal := (← mkFreshExprMVar (mkConst ``True)).mvarId!
  let entry : DiskLookup.Entry := {module := "Fixture", name := "capped", parts := #[]}
  let capped ← boundedLookupCandidate table entry goal do
    IO.addHeartbeats (lookupCandidateBudget * 1000 + 1)
    checkSystem "lookup.candidate.cap-fixture"
    return {complete := true}
  unless !capped.complete && capped.capped.size == 1 do
    throwError "cap became normal failure"
  let failed ← boundedLookupCandidate table {entry with name := "unsupported"} goal do
    throwError "lookup.view_depth_incomplete"
  unless !failed.complete && failed.failures.size == 1 do
    throwError "candidate exception escaped or disappeared"
  let prepared ← boundedLookupCandidate table {entry with name := "preparation"} goal do
    withLookupPreparation (some budget) do
      IO.addHeartbeats (lookupPreparationBudget * 1000 + 1)
      checkSystem "lookup.preparation.cap-fixture"
    return {complete := true}
  unless !prepared.complete && prepared.capped.size == 1 do
    throwError "preparation cap became normal failure"
  let recovered ← boundedLookupCandidate table {entry with name := "recovered"} goal do
    unless !(← goal.isAssigned) do throwError "failed state survived"
    goal.assign (mkConst ``True.intro)
    return {complete := true, source? := some ``True.intro}
  unless recovered.complete && recovered.source?.isSome do
    throwError "earlier failure starved a later checked candidate"
  logInfo "LOOKUP_V7_REGRESSION cap=unknown exception=local preparation=unknown later_candidate=checked"
