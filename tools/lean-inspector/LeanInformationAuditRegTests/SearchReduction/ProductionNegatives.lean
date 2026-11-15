import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.ProductionNegativeCandidates
import LeanInformationAuditRegTests.SearchReduction.Candidates

/-! Opt-in production calibrations. A safe verdict and coverage of a budget
stop are separate results. No heartbeat injection or alternate index is used. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction.ProductionNegativeCandidates
set_option Elab.async false

/-- An unclassified diagnostic until a target-only B-only certificate succeeds.
The label and graph share production baseline selection and vocabulary transport;
label attempts never enter the graph request's certificate pool. -/
private unsafe def formulaLabel (request : Request) : CommandElabM Bool := do
  let source ← getEnv
  let delivery := (#[request.target] ++ request.additions).filterMap fun n =>
    (source.getModuleIdxFor? n).map (source.header.moduleNames[·.toNat]!)
  let ancestors ← targetBaselineImports request.baselineCommit delivery source
    request.target request.baseline
  let modules := ((ancestors.filter (·.toString.startsWith "D5.")) ++
    request.baseline).foldl
      (fun out n => if out.contains n then out else out.push n) (#[] : Array Name)
  enableInitializersExecution
  let imports : Array Import := #[{module := `Mathlib}] ++
    modules.map (fun n => {module := n})
  let base ← importModules imports options 0 (leakEnv := false) (loadExts := true)
  let catalog ← baselineCatalog request.baselineCommit delivery base
  let some directory ← IO.getEnv "SEARCH_REDUCTION_INDEX"
    | throwError "formula diagnostic requires the production index"
  let index ← DiskLookup.openIndex directory request.baselineCommit mathlibRevision
    catalog.excluded
  let prepared ← prepare source base request false
  let .ok (clean, target, _) := prepared
    | throwError "formula label vocabulary preparation failed"
  let work : CoreM Bool := MetaM.run' do
    withEnv clean do
      let budget ← IO.mkRef ({} : LookupBudgetState)
      let table : LookupTable := {
        environment := base, disk? := some index,
        implicationModules? := some ancestors, budget? := some budget}
      let automatic ← certifyLocal target.type [] (some table)
      let mut valid := automatic.cost == .zero && automatic.proof?.isSome
      if let some proof := automatic.proof? then checkLocalProof target.type proof
      let mut checks := #[Json.mkObj [
        ("certificate", toJson "by_close + automatic full-statement membership"),
        ("cost", toJson (reprStr automatic.cost)), ("detail", toJson automatic.detail)]]
      let certificates : Array ObviousCertificate := #[.close,
        .lookup `Nat.add_mod, .lookup `Nat.mod_eq_of_lt, .lookup `Nat.mod_mod]
      for certificate in certificates do
        let result ← replayCertificate target.type [] certificate (some table)
        if result.cost == .zero then
          let some proof := result.proof? | throwError "zero label without proof"
          checkLocalProof target.type proof
          valid := true
        checks := checks.push (Json.mkObj [
          ("certificate", toJson certificate.render),
          ("cost", toJson (reprStr result.cost)), ("detail", toJson result.detail)])
      let telescope ← forallTelescopeReducing target.type fun xs _ => pure xs.size
      IO.println s!"FORMULA_LABEL {Json.mkObj [
        ("target", toJson request.target.toString),
        ("label_target", toJson request.target.toString),
        ("target_type_hash", toJson (hash target.type)), ("telescope_size", toJson telescope),
        ("scope", toJson "B_T"), ("baseline_modules", toJson (modules.map (·.toString))),
        ("lookup_version", toJson lookupVersion),
        ("certificate_language", toJson certificateLanguageVersion),
        ("transport_version", toJson transportVersion),
        ("label_B_only_kernel_checked", toJson valid), ("checks", toJson checks),
        ("scope_limit", toJson "Only the listed target certificates were attempted; \
          failure is not absence of short certificates.")
        ] |>.compress}"
      (← IO.getStdout).flush
      pure valid
  let context : Core.Context := {
    fileName := "<formula target label>", fileMap := default,
    options := options.set `maxHeartbeats 0,
    initHeartbeats := ← IO.getNumHeartbeats, maxHeartbeats := 0}
  match ← (work.run context {env := clean}).toIO' with
  | .ok (valid, state) =>
    if state.messages.hasErrors then throwError "formula label elaboration failed"
    return valid
  | .error ex => throwError "formula label replay failed: {ex.toMessageData}"

/-- Run label and graph in separate processes. A valid target label together
with an exhaustive reduction is an E veto, never a calibration pass. -/
private unsafe def formulaDiagnostic (labelOnly : Bool) : CommandElabM Unit := do
  let request : Request := {
    target := ``ladderOddViaFormula, additions := #[``ladderClosedForm],
    «baseline» := #[`Mathlib.Data.Nat.Sqrt],
    baselineCommit := "b02b98342945a1a724a227db4fa38e376640e573"}
  if labelOnly then
    discard <| formulaLabel request
    return
  let resultName := `productionNegative.kappaFormula
  executeProbe request #[`LeanInformationAuditRegAnalysis.SearchReduction.Commands,
    `LeanInformationAuditRegTests.SearchReduction.ProductionNegativeCandidates,
    `LeanInformationAuditRegTests.SearchReduction.Candidates] resultName false
  let reading ← liftTermElabM <| evalConst GraphReading (resultName ++ `graphReading)
  let disposition := classifyDisposition reading
  logInfo s!"FORMULA_DIAGNOSTIC {Json.mkObj [
    ("case", toJson "kappa-formula"),
    ("classification", toJson "diagnostic-requires-separate-target-label"),
    ("A1", toJson (reprStr (classifyDisposition (priceMappingV18 reading)))),
    ("B", toJson (reprStr disposition)), ("basis_budget", toJson (budgetBasis reading)),
    ("structure_checked", toJson reading.structureChecked),
    ("structure_clean", toJson reading.structureClean),
    ("target_part_complete", toJson reading.targetPartComplete),
    ("graph_complete", toJson reading.graph.complete),
    ("pool_size", toJson request.certificates.size),
    ("index_scope", toJson "production/index-v19")
    ] |>.compress}"

set_option maxHeartbeats 0 in
run_cmd do
  let some selected ← IO.getEnv "SEARCH_REDUCTION_NEGATIVE_CASE"
    | return
  if selected.isEmpty then return
  if selected == "kappa-formula" || selected == "kappa-formula-label" then
    formulaDiagnostic (selected == "kappa-formula-label")
    return
  let fixtures : Array (String × Name × Array Name × ObviousCertificate × String) := #[
    ("kappa", ``squareVia, #[``squareFact], .lookup ``Nat.exists_mul_self, "searchKappa"),
    ("G", ``squareVia, #[``squareFact], .lookup ``Nat.exists_mul_self, "coveragePrefixG"),
    ("G-control", ``squareVia, #[``squareFact], .lookup ``Nat.exists_mul_self, "positive-control"),
    ("kappa-large", ``squareViaLarge, #[``squareFactLarge], .lookup ``Nat.exists_mul_self, "searchKappa"),
    ("G-large", ``squareViaLarge, #[``squareFactLarge], .lookup ``Nat.exists_mul_self, "coveragePrefixG"),
    ("G-large-control", ``squareViaLarge, #[``squareFactLarge], .lookup ``Nat.exists_mul_self, "positive-control"),
    ("packed", ``sqrtTarget, #[``packed], .lookup ``Nat.sqrt_eq, "reverse-kappa-or-G"),
    ("bounds", ``sqrtTarget, #[``bounds], .lookup ``Nat.sqrt_eq, "reverse-kappa-or-G"),
    ("iff", ``sqrtTarget, #[``reverseIff], .lookup ``Nat.sqrt_eq, "reverse-kappa-or-G"),
    ("split", ``sqrtTarget, #[``lower, ``upper], .lookup ``Nat.sqrt_eq, "reverse-kappa-or-G"),
    ("wide-packed", ``sqrtTarget, #[``widePacked], .lookup ``Nat.sqrt_eq, "reverse-kappa-or-G"),
    ("expensive", ``expensiveVia, #[``cachedInstance], .close, "baseline-hit"),
    ("unwrapped", ``LeanInformationAudit.Tests.SearchReduction.Candidates.unwrapped,
      #[], .close, "zero-intervals")]
  let some (_, target, additions, label, intendedStop) := fixtures.find? (·.1 == selected)
    | throwError "unknown production-negative case: {selected}"
  let some directory ← IO.getEnv "SEARCH_REDUCTION_INDEX"
    | throwError "production calibration requires an explicit SEARCH_REDUCTION_INDEX"
  let source ← getEnv
  let basis := "b02b98342945a1a724a227db4fa38e376640e573"
  let index ← DiskLookup.openIndex directory basis mathlibRevision
  -- The label is checked separately. It does not enter the production pool.
  enableInitializersExecution
  let labelBase ← importModules #[{module := `Mathlib.Tactic}, {module := `Mathlib.Data.Nat.Sqrt}] {} 0
    (leakEnv := false) (loadExts := true)
  liftTermElabM do
    withEnv labelBase do
      let info := (source.find? target).get!
      let type ← copyStatement source target info.type
      let labelBudget ← IO.mkRef ({} : LookupBudgetState)
      let checked ← replayCertificate type [] label (some {
        environment := labelBase, disk? := some index,
        implicationModules? := some labelBase.header.moduleNames,
        budget? := some labelBudget})
      unless checked.cost == .zero && checked.proof?.isSome do
        throwError "B-only label certificate failed: {selected}: {checked.detail}"
      checkLocalProof type checked.proof?.get!
  let request : Request := {
    target, additions,
      «baseline» := if selected == "unwrapped" then #[] else #[`Mathlib.Data.Nat.Sqrt],
    baselineCommit := basis,
    certificates := if selected == "G-control" || selected == "G-large-control" then
      #[⟨label, "G-trap-control"⟩] else #[]}
  -- This is the same startup, source audit and kernel publication as research
  -- requests. Explicit false selects the production population and scheduler.
  let resultName := `productionNegative ++ selected.toName
  executeProbe request #[`LeanInformationAuditRegAnalysis.SearchReduction.Commands,
    `LeanInformationAuditRegTests.SearchReduction.ProductionNegativeCandidates,
    `LeanInformationAuditRegTests.SearchReduction.Candidates] resultName false
  let reading ← liftTermElabM <| evalConst GraphReading (resultName ++ `graphReading)
  let disposition := classifyDisposition reading
  let a1 := classifyDisposition (priceMappingV18 reading)
  let kappa := reading.queryRecords.any (·.encounteredSearchKappa)
  let coverage := reading.queryRecords.any (·.encounteredCoveragePrefixG)
  let reverseBudget := reading.queryRecords.any fun query =>
    query.role.startsWith "target-part-reverse:" &&
      (query.encounteredSearchKappa || query.encounteredCoveragePrefixG)
  let reverseScheduled := reading.queryRecords.any (·.role.startsWith "target-part-reverse:")
  let baselinePositive := match reading.baseline.upper with
    | .finite n => decide (n > 0)
    | .top => false
  let pairedImproves := better reading.paired.upper reading.baseline.upper
  let guardDecided := reverseScheduled && baselinePositive && pairedImproves &&
    disposition == .incomplete && !reading.targetPartComplete &&
    reading.graph.complete && reading.presentationComplete && reading.isolated &&
    reading.structureChecked && reading.structureClean
  let kappaThenHit := reading.queryRecords.any fun query =>
    query.encounteredSearchKappa && (match query.terminal with | .hit _ => true | _ => false)
  let reached := match intendedStop with
    | "searchKappa" => kappaThenHit && disposition == .bindOnly
    | "coveragePrefixG" => coverage
    | "reverse-kappa-or-G" => reverseBudget && guardDecided
    | "positive-control" | "baseline-hit" | "zero-intervals" => disposition == .bindOnly
    | _ => false
  logInfo s!"PRODUCTION_NEGATIVE {Json.mkObj [
    ("case", toJson selected), ("target", toJson target.toString),
    ("label_certificate", toJson label.render), ("label_B_only_kernel_checked", toJson true),
    ("intended_stop", toJson intendedStop), ("targeted_stop_covered", toJson reached),
    ("coverage_gap", toJson (!reached)), ("encountered_search_kappa", toJson kappa),
    ("encountered_coverage_prefix_G", toJson coverage),
    ("kappa_followed_by_hit", toJson kappaThenHit),
    ("reverse_budget_stop", toJson reverseBudget),
    ("reverse_scheduled", toJson reverseScheduled),
    ("baseline_upper_positive", toJson baselinePositive),
    ("paired_upper_improves", toJson pairedImproves),
    ("target_part_complete", toJson reading.targetPartComplete),
    ("guard_decided", toJson guardDecided),
    ("query_stop_records", toJson (reading.queryRecords.map fun query => Json.mkObj [
      ("role", toJson query.role), ("terminal", toJson (reprStr query.terminal)),
      ("search_kappa", toJson query.encounteredSearchKappa),
      ("coverage_prefix_G", toJson query.encounteredCoveragePrefixG)])),
    ("A1", toJson (reprStr a1)), ("B", toJson (reprStr disposition)),
    ("pool_control", toJson (selected == "G-control" || selected == "G-large-control")),
    ("structure_checked", toJson reading.structureChecked),
    ("structure_clean", toJson reading.structureClean),
    ("index_digest", toJson index.header.digest), ("index_inputs", toJson index.header.inputs),
    ("stop_coverage_scope", toJson "same-key slow-before-easy and easy-beyond-G remain unverified unless actual candidate telemetry establishes their positions")
    ] |>.compress}"

  if selected == "G" || selected == "G-large" then
    if disposition == .reductionR && !budgetBasis reading then
      throwError "G trap produced an exhaustive reduction"
  else if disposition == .reductionR then
    throwError "negative calibration produced a reduction: {selected}"
  if selected == "G-control" || selected == "G-large-control" || selected == "expensive" then
    unless disposition == .bindOnly do throwError "positive label control did not erase gain: {selected}"
  if selected == "unwrapped" then
    unless reading.baseline.lower == .finite 0 && reading.baseline.upper == .finite 0 &&
        reading.paired.lower == .finite 0 && reading.paired.upper == .finite 0 do
      throwError "unwrapped lost its [0,0]/[0,0] intervals"
