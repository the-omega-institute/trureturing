import LeanInformationAuditRegAnalysis.SearchReduction.Commands

/-! Observe-only replay of consumed budget prices. This entry never publishes
a replacement reading, a certificate nomination, or a persistent cache record. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta Elab Command

abbrev sensitivityVersion : String := "R_lookup-sensitivity/v1/4kappa-4G/consumed-budget-prices"

structure SensitivityQuery where
  roles : List String
  target : Expr
  premises : List Expr
  original : RQuery

/-- Reconstruct exact statements from typed graph data, then require the
corresponding executed record. Hashes check consistency, never select expressions. -/
def sensitivityQueriesV1 (reading : GraphReading) : Except String (List SensitivityQuery) := do
  let vertex := fun id => do
    let some v := reading.graph.vertices.find? (·.id == id)
      | throw s!"sensitivity.v1.missing_vertex:{id}"
    pure v.type
  let make := fun role target premises original => do
    unless reading.queryRecords.any (fun q => q.role == role && q.target == target.hash &&
        q.premises == premises.map Expr.hash && q.terminal == original) do
      throw s!"sensitivity.v1.executed_record_mismatch:{role}"
    pure ({roles := [role], target, premises, original} : SensitivityQuery)
  let mut queries := []
  if reading.baselineProbe.outcome == .exhausted && reading.baselineProbe.query.budget then
    queries := queries ++ [← make "baseline-root" (← vertex reading.graph.root)
      (← (armSeeds reading.graph false).mapM vertex) reading.baselineProbe.query]
  for edge in reading.graph.edges do
    if edge.pairedCost == .one && edge.pairedQuery.budget then
      throw "sensitivity.v1.unsupported_paired_negative_record"
    if edge.cost == .one && edge.query.budget then
      queries := queries ++ [← make s!"author-edge:{edge.source}:{edge.conclusion}"
        (← vertex edge.conclusion)
        (← (statementPremises edge (armSeeds reading.graph false)).mapM vertex) edge.query]
  let mut unique : List SensitivityQuery := []
  for query in queries do
    if let some previous := unique.find? (fun q =>
        q.target == query.target && q.premises == query.premises) then
      unless previous.original == query.original do
        throw "sensitivity.v1.inconsistent_duplicate_terminal"
      unique := unique.map fun q =>
        if q.target == query.target && q.premises == query.premises then
          {q with roles := q.roles ++ query.roles} else q
    else unique := unique ++ [query]
  return unique

/-- A fault is inconclusive, rather than a successful flip or a confirmed miss. -/
def sensitivityPriceFlipV1 (terminal : RQuery) : Option Bool :=
  terminal.price.map (· == 0)

private def readingSummary (r : GraphReading) : Json := Json.mkObj [
  ("verdict", toJson (reprStr (classifyDisposition r))),
  ("basis", toJson (if budgetBasis r then "budget" else "exhaustive")),
  ("closure", toJson (reprStr (classifyClosure r))),
  ("baseline_interval", toJson (reprStr r.baseline)),
  ("paired_interval", toJson (reprStr r.paired))]

unsafe def diagnoseReadingV1 (table : LookupTable) (shared : Option ImportState)
    (reading : GraphReading) : MetaM Json := do
  unless table.allocation == .production do
    throwError "sensitivity.v1.original_must_use_production_allocations"
  let before := toExpr reading
  let pool := (← certificateNominations.get).map CertificateNomination.encode
  let bindings := (← edgeCertificateNominations.get).map fun (n, c) => (n, c.encode)
  let records := toExpr (← currentQueryRecords.get)
  let ordinal ← lookupAttemptOrdinal.get
  let eligible := classifyDisposition reading == .reductionR && budgetBasis reading
  let queries ← if eligible then ofExcept (sensitivityQueriesV1 reading) else pure []
  let mut reports := #[]
  for query in queries do
    let diagnostic ← onDemandLookup {
      environment := table.environment, allocation := .sensitivity4xV1,
      complete := table.complete, enabled := table.enabled, disk? := table.disk?,
      fixture := table.fixture, implicationModules? := table.implicationModules?} shared
    let result ← try sensitivityRebuildV1 query.target query.premises diagnostic
      finally if let some close := diagnostic.close? then close
    let report := Json.mkObj [
      ("roles", toJson query.roles), ("target_hash", toJson query.target.hash),
      ("premise_hashes", toJson (query.premises.map Expr.hash)),
      ("original_terminal", toJson (reprStr query.original)),
      ("original_price", toJson query.original.price),
      ("diagnostic_terminal", toJson (reprStr result.query)),
      ("diagnostic_price", toJson result.query.price),
      ("price_flipped_to_hit", toJson (sensitivityPriceFlipV1 result.query)),
      ("detail", toJson result.detail)]
    reports := reports.push report
    emitLookupRecord s!"SEARCH_REDUCTION_SENSITIVITY_V1_QUERY {report.compress}"
  unless before == toExpr reading &&
      pool == (← certificateNominations.get).map CertificateNomination.encode &&
      bindings == ((← edgeCertificateNominations.get).map fun (n, c) => (n, c.encode)) &&
      records == toExpr (← currentQueryRecords.get) && ordinal == (← lookupAttemptOrdinal.get) do
    throwError "sensitivity.v1.production_state_changed"
  return Json.mkObj [
    ("version", toJson sensitivityVersion), ("eligible_budget_positive", toJson eligible),
    ("original_reading", readingSummary reading),
    ("candidate_kappa", toJson (4 * lookupCandidateBudget)),
    ("coverage_G", toJson (4 * lookupCoverageBudget)),
    ("preparation", toJson lookupPreparationBudget),
    ("local_closure", toJson localBudget),
    ("query_count", toJson queries.length), ("queries", toJson reports),
    ("flip_meaning", toJson "price 1 becomes checked Hit price 0; null means Fault/NotRun"),
    ("production_state_unchanged", toJson true),
    ("persistent_cache_reads_and_writes", toJson false),
    ("replacement_production_reading_published", toJson false)]

/-- Invoke through make search-reduction-sensitivity-v1. The request is Lean
data, and its original reading is recomputed at the frozen production budgets. -/
unsafe def executeSensitivityV1 (request : Request) (owners : Array Name) : CommandElabM Unit := do
  unless (← IO.getEnv "SEARCH_REDUCTION_DIAGNOSTIC_ENTRY") == some "sensitivity-v1" do
    throwError "sensitivity.v1.use_dedicated_make_entry"
  for optionName in ["SEARCH_REDUCTION_QUERY_CACHE", "SEARCH_REDUCTION_RESUME"] do
    unless (← IO.getEnv optionName) == some "" do
      throwError "sensitivity.v1.persistent_cache_must_be_disabled:{optionName}"
  unless (← IO.getEnv "SEARCH_REDUCTION_PROBE_CACHE") == some "0" &&
      (← IO.getEnv "SEARCH_REDUCTION_PROBE_READ").isNone &&
      (← IO.getEnv "SEARCH_REDUCTION_PROBE_WRITE").isNone do
    throwError "sensitivity.v1.probe_cache_must_be_disabled"
  let imports := owners.map fun module => {module : Import}
  let (source, shared) ← withImporting do
    let (_, shared) ← (importModulesCore #[{module := `Mathlib}]).run default
    let (_, state) ← (importModulesCore imports).run shared
    let source ← finalizeImport state imports options 0 (leakEnv := false) (loadExts := true)
    pure (source, shared)
  let report ← IO.mkRef (none : Option Json)
  let original ← run source request shared (diagnostic? := some fun table imports reading => do
    report.set (some (← diagnoseReadingV1 table imports reading)))
  let some report ← report.get
    | throwError "sensitivity.v1.original_reading_failed:{original.reason}"
  emitLookupRecord s!"SEARCH_REDUCTION_SENSITIVITY_V1 {report.compress}"

end LeanInformationAudit.SearchReduction
