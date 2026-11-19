import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.LookupBaseline
import LeanInformationAuditRegTests.SearchReduction.ExecutionChainTests

/-! Recall, nonrecursive closure and incomplete-basis regression checks. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction.LookupBaseline
set_option Elab.async false
set_option maxHeartbeats 0

run_cmd do
  let directory : System.FilePath :=
    "build/lean-inspector/search-reduction-test-index/legacy-production-header"
  IO.FS.createDirAll directory
  let basis := "b530df86e6e9c4709edecd3009bb96c3d4ebc8be"
  let frozen ← IO.Process.output {cmd := "git", args :=
    #["ls-tree", "-r", "--name-only", basis, "--", "Golden/Frozen/state/D5"]}
  unless frozen.exitCode == 0 do throwError "legacy header fixture: {frozen.stderr}"
  let mut modules := #["Mathlib"]
  for path in frozen.stdout.trimAscii.toString.splitOn "\n" do
    if path.endsWith ".lean.json" then
      modules := modules.push (((path.drop "Golden/Frozen/state/".length).toString.dropEnd
        ".lean.json".length).toString.replace "/" ".")
  let text := (toJson ({} : DiskLookup.Manifest)).compress
  IO.FS.writeFile (directory / "manifest.json") text
  let header : DiskLookup.Header := {
    basis, mathlib := mathlibRevision, inputs := 0, storage := ".", root := "manifest.json",
    digest := hash text, complete := true, modules := modules.size,
    declarations := 0, indexed := 0, missing := #[]}
  let fields ← IO.ofExcept (toJson header).getObj?
  IO.FS.writeFile (directory / "header.json")
    (Json.mkObj (fields.toArray.toList.filter (fun field => field.1 != "scope"))).compress
  IO.FS.writeFile (directory / "import-partitions.json") (toJson #[modules]).compress
  let index ← DiskLookup.openIndex directory basis mathlibRevision
  unless index.header.scope == "" && index.header.modules == modules.size do
    throwError "legacy production header lost its original population"
  logInfo "LOOKUP_LEGACY_PRODUCTION missing_scope=accepted population=checked"

run_cmd do
  let directory : System.FilePath :=
    "build/lean-inspector/search-reduction-test-index/legacy-scoped-rejection"
  IO.FS.createDirAll directory
  let manifest : DiskLookup.Manifest := {}
  let text := (toJson manifest).compress
  IO.FS.writeFile (directory / "manifest.json") text
  let header : DiskLookup.Header := {
    basis := "b530df86e6e9c4709edecd3009bb96c3d4ebc8be",
    mathlib := mathlibRevision, inputs := 0, storage := ".", root := "manifest.json",
    digest := hash text, complete := true, modules := 1,
    declarations := 0, indexed := 0, missing := #[]}
  IO.FS.writeFile (directory / "header.json") (toJson header).compress
  IO.FS.writeFile (directory / "import-partitions.json")
    (toJson (#[#["Mathlib"]] : Array (Array String))).compress
  let rejected ← try
    discard <| DiskLookup.openIndex directory header.basis mathlibRevision
    pure false
    catch _ => pure true
  unless rejected do throwError "production accepted a complete=true scoped test snapshot"
  logInfo "LOOKUP_PRODUCTION_SCOPE legacy_scoped=rejected complete_true=true"
  IO.FS.writeFile (directory / "header.json") (toJson {header with scope := "test"}).compress
  let fixture ← DiskLookup.openFixtureIndex directory header.basis mathlibRevision
  unless fixture.header.complete do throwError "test API lost its complete fixture"
  let rejected ← try
    discard <| DiskLookup.openIndex directory header.basis mathlibRevision
    pure false
    catch _ => pure true
  unless rejected do throwError "production accepted an explicitly tagged test snapshot"
  let production ← resolveLookupTable {environment := ← getEnv}
  unless production.disk?.isNone && !production.complete do
    throwError "missing production index fell back to a test fixture"
  logInfo "LOOKUP_PRODUCTION_SCOPE tagged_scoped=rejected fallback=none test_api=accepted"

run_cmd liftTermElabM do
  let timeout : MetaM LocalResult := do
    IO.addHeartbeats (localBudget * 1000 + 1)
    checkSystem "lookup.isolation.fixture"
    return {cost := .one}
  let exhausted : MetaM LocalResult := pure {
    cost := .one, query := .miss .exhaustive, detail := "exhausted"}
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
  unless result.cost == .unknown && result.detail == "local-closure-heartbeat" do
    throwError "candidate vocabulary copy escaped the enclosing allocation"
  logInfo "LOOKUP_COPY_BUDGET enclosing=true timeout=unknown"

run_cmd liftTermElabM do
  let directory : System.FilePath := "build/lean-inspector/search-reduction-test-index/colliding-owner-fixture"
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
  unless exceeded.cost == .unknown && exceeded.detail == "candidate-preparation-limit" do
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
  unless !capped.complete && capped.capped.size == 1 &&
      capped.failures == #["Fixture:capped:candidate-search-kappa"] do
    throwError "cap became normal failure: complete={capped.complete}; capped={capped.capped}; reasons={capped.failures}"
  let failed ← boundedLookupCandidate table {entry with name := "unsupported"} goal do
    throwError "lookup.view_depth_incomplete"
  unless !failed.complete && failed.failures.size == 1 do
    throwError "candidate exception escaped or disappeared"
  let prepared ← boundedLookupCandidate table {entry with name := "preparation"} goal do
    withLookupPreparation (some budget) do
      IO.addHeartbeats (lookupPreparationBudget * 1000 + 1)
      checkSystem "lookup.preparation.cap-fixture"
    return {complete := true}
  unless !prepared.complete && prepared.capped.size == 1 &&
      prepared.failures == #["Fixture:preparation:candidate-preparation-limit"] do
    throwError "preparation cap became normal failure"
  let recovered ← boundedLookupCandidate table {entry with name := "recovered"} goal do
    unless !(← goal.isAssigned) do throwError "failed state survived"
    goal.assign (mkConst ``True.intro)
    return {complete := true, source? := some ``True.intro}
  unless recovered.complete && recovered.source?.isSome do
    throwError "earlier failure starved a later checked candidate"
  logInfo "LOOKUP_V7_REGRESSION cap=unknown exception=local preparation=unknown later_candidate=checked"


/- These boundary probes use real checked propositions and the unchanged
allocations. Injected heartbeat charges test the execution boundary; they do
not establish production coverage of a slow-before-easy candidate population. -/
run_cmd liftTermElabM do
  let type := mkConst ``True
  let table : LookupTable := {environment := ← getEnv}
  let goal ← mkFreshExprMVar type
  let slow : DiskLookup.Entry := {module := "boundary", name := "slow", parts := #[]}
  let easy : DiskLookup.Entry := {module := "boundary", name := "easy", parts := #[]}
  let capped ← boundedLookupCandidate table slow goal.mvarId! do
    IO.addHeartbeats (lookupCandidateBudget * 1000 + 1)
    checkSystem "v19.candidate-search-kappa"
    return {complete := true}
  unless capped.searchKappa && capped.faults.isEmpty && !capped.complete do
    throwError "candidate kappa was not recorded as a typed search stop"
  let hit ← boundedLookupCandidate table easy goal.mvarId! do
    goal.mvarId!.assign (mkConst ``True.intro)
    return {complete := true, source? := some ``True.intro}
  let continued := mergeLookupTrace capped hit
  unless continued.source?.isSome && continued.searchKappa do
    throwError "successor certificate was lost after candidate kappa"
  let short ← replayCertificate type [] .close
  unless short.cost == .zero && short.query.price == some 0 do
    throwError "B-only by_close certificate failed"
  let budgetMiss : LookupTrace := {
    scheduled := true, searchKappa := true, coveragePrefixG := true}
  unless budgetMiss.terminal == .miss .coveragePrefixG do
    throwError "coverage stop kind was not retained"
  let fault := {budgetMiss with faults := #["preparation-fault"]}
  unless fault.terminal.price.isNone do
    throwError "unabsorbed fault was hidden by a later budget stop"
  for reason in ["missing-data", "preparation-failed", "oom", "cancelled"] do
    unless (RQuery.fault reason).price.isNone do throwError "fault was priced"
  unless ({} : LookupTrace).terminal == .notRun && RQuery.notRun.price.isNone do
    throwError "unscheduled query was priced"
  let exhausted : MetaM LocalResult := pure {
    cost := .one, query := .miss .exhaustive}
  let unscheduled ← independentRebuild exhausted (pure {query := .notRun})
  unless unscheduled.cost == .unknown && unscheduled.query.price.isNone do
    throwError "unscheduled lookup acquired a price through the local branch"
  let big := mkNatLit 1000000000000000000000000000000000000
  let application ← mkAppM ``Nat.add_assoc #[big, big, big]
  let instanceType ← inferType application
  let trivial ← replayCertificate instanceType [] .close
  unless trivial.cost == .zero do throwError "large general-lemma instance was priced hard"
  logInfo "R_V19_BOUNDARIES kappa=actual-injected-charge successor=kernel-hit B_only=by_close G=typed-prefix-record faults=unpriced notRun=unpriced large-instance=zero production-stop-coverage=open"
