import LeanInformationAuditRegAnalysis.SearchReduction.Sensitivity
import LeanInformationAuditRegTests.SearchReduction.ExecutionChainCandidates

/-! Diagnostic allocation, consumed-query selection, and production isolation. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction.ExecutionChainCandidates
set_option Elab.async false

private def consumed : GraphReading := {
  graph := {
    root := 0, vertices := [{id := 0, type := mkConst ``True}],
    edges := [{conclusion := 0, cost := .one, query := .miss .searchKappa}]},
  baselineProbe := {outcome := .exhausted, query := .miss .searchKappa},
  queryRecords := [
    {role := "baseline-root", target := (mkConst ``True).hash,
      premises := [], terminal := .miss .searchKappa},
    {role := "author-edge:none:0", target := (mkConst ``True).hash,
      premises := [], terminal := .miss .searchKappa},
    {role := "target-part-reverse:99", target := 0,
      premises := [], terminal := .miss .coveragePrefixG}]}

run_cmd do
  let queries ← ofExcept (sensitivityQueriesV1 consumed)
  unless queries.length == 1 && queries.any (fun q => q.roles.length == 2) do
    throwError "SENSITIVITY consumed queries must deduplicate exact expressions and exclude guards"
  unless sensitivityPriceFlipV1 (.hit .close) == some true &&
      sensitivityPriceFlipV1 (.miss .exhaustive) == some false &&
      sensitivityPriceFlipV1 (.fault "test") == none &&
      sensitivityPriceFlipV1 .notRun == none do
    throwError "SENSITIVITY Fault/NotRun cannot become a confirmed result"
  match sensitivityQueriesV1 {consumed with queryRecords := []} with
  | .ok _ => throwError "SENSITIVITY missing executed record accepted"
  | .error _ => pure ()
  logInfo "SENSITIVITY selection PASS exact-dedup consumed-only \
    missing-record-rejected fault-unpriced"

set_option maxHeartbeats 0 in
-- The wrapper owns each candidate allocation, including synthetic heartbeat charges.
run_cmd liftTermElabM do
  let env ← getEnv
  let table : LookupTable := {environment := env}
  unless table.allocation.candidate == 200000 && table.allocation.coverage == 340000000 &&
      LookupAllocation.sensitivity4xV1.candidate == 800000 &&
      LookupAllocation.sensitivity4xV1.coverage == 1360000000 &&
      lookupPreparationBudget == 8000000 && localBudget == 200000 do
    throwError "SENSITIVITY frozen production allocations changed"
  let entry : DiskLookup.Entry := {
    module := "Init.Prelude", name := "True.intro", parts := #[("True", 0), ("intro", 0)]}
  let attempt := fun (allocation : LookupAllocation) => do
    let goal ← mkFreshExprMVar (mkConst ``True)
    boundedLookupCandidate {table with allocation} entry goal.mvarId! do
      IO.addHeartbeats 250000000
      checkSystem "SENSITIVITY candidate charge"
      goal.mvarId!.assign (mkConst ``True.intro)
      return {complete := true, source? := some ``True.intro}
  let production ← attempt .production
  let ordinal ← lookupAttemptOrdinal.get
  let diagnostic ← attempt .sensitivity4xV1
  unless (← lookupAttemptOrdinal.get) == ordinal do
    throwError "SENSITIVITY diagnostic changed production checkpoint ordinal"
  let productionAfter ← attempt .production
  unless production.searchKappa && production.source?.isNone &&
      diagnostic.source? == some ``True.intro && !diagnostic.searchKappa &&
      productionAfter.searchKappa && productionAfter.source?.isNone do
    throwError "SENSITIVITY candidate allocation leaked into production"
  let records := toExpr (← currentQueryRecords.get)
  let pool := (← certificateNominations.get).map CertificateNomination.encode
  let answerDirectory? ← IO.getEnv "SEARCH_REDUCTION_QUERY_CACHE"
  let answerExisted ← answerDirectory?.mapM fun directory =>
    (System.FilePath.mk directory).pathExists
  let result ← sensitivityRebuildV1 (mkConst ``True) []
    {table with allocation := .sensitivity4xV1}
  unless result.cost == .zero && result.query.price == some 0 &&
      records == toExpr (← currentQueryRecords.get) &&
      pool == (← certificateNominations.get).map CertificateNomination.encode do
    throwError "SENSITIVITY raw replay changed production records or certificate pool"
  if let some directory := answerDirectory? then
    unless directory.isEmpty do
      unless some (← (System.FilePath.mk directory).pathExists) == answerExisted do
        throwError "SENSITIVITY diagnostic wrote production answer-cache directory"
  logInfo "SENSITIVITY kappa PASS production-cap diagnostic-kernel-hit \
    production-cap-again state-isolated"

private unsafe def coverageTable : MetaM LookupTable := do
  let env ← getEnv
  let some owner := env.getModuleIdxFor? ``easy
    | throwError "SENSITIVITY fixture owner missing"
  let entry : DiskLookup.Entry := {
    module := env.header.moduleNames[owner.toNat]!.toString,
    name := (``easy).toString,
    parts := ((``easy).toString.splitOn ".").toArray.map (fun p => (p, 0))}
  let keys ← DiscrTree.mkPath (mkApp (mkConst ``Target) (mkNatLit 7))
  let tree := ({} : DiscrTree DiskLookup.Entry).insertKeyValue keys entry
  let directory : System.FilePath :=
    s!"build/lean-inspector/search-reduction-test-index/sensitivity-v1-{← IO.monoNanosNow}"
  IO.FS.createDirAll directory
  pickle (directory / "primary.pickle") ({tree} : DiskLookup.PickledShard)
  let index : DiskLookup.Index := {
    directory, header := {
      scope := "test", basis := sensitivityVersion, mathlib := mathlibRevision,
      inputs := 1, storage := ".", root := "", digest := 1, complete := true,
      modules := 1, declarations := 1, indexed := 1, missing := #[]},
    manifest := #[(hash keys[0]!, #["primary.pickle"])]}
  return {environment := env, fixture := true, disk? := some index}

set_option maxHeartbeats 0 in
-- Independent κ/G wrappers own the budgets being tested.
run_cmd liftTermElabM do
  let table ← coverageTable
  let attempt := fun (allocation : LookupAllocation) => do
    let budget ← IO.mkRef ({coverage := lookupCoverageBudget * 1000} : LookupBudgetState)
    let goal ← mkFreshExprMVar (mkApp (mkConst ``Target) (mkNatLit 7))
    lookupLeafPass {table with allocation, budget? := some budget} goal.mvarId!
      (fun _ => pure false) (fun g => do
        g.assign (mkApp (mkConst ``easy) (mkNatLit 7))
        pure true)
  let production ← attempt .production
  let diagnostic ← attempt .sensitivity4xV1
  let productionAfter ← attempt .production
  unless production.coveragePrefixG && production.source?.isNone &&
      diagnostic.source? == some ``easy && !diagnostic.coveragePrefixG &&
      productionAfter.coveragePrefixG && productionAfter.source?.isNone do
    throwError "SENSITIVITY G allocation leaked into production"
  logInfo "SENSITIVITY G PASS production-prefix diagnostic-kernel-hit production-prefix-again"
