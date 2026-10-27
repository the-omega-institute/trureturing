import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.ProductionNegativeCandidates
import LeanInformationAuditRegTests.SearchReduction.Candidates

/-! Opt-in production calibrations. A safe verdict and coverage of a budget
stop are separate results. No heartbeat injection or alternate index is used. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction.ProductionNegativeCandidates
set_option Elab.async false
set_option maxHeartbeats 0 in
run_cmd do
  let some selected ← IO.getEnv "SEARCH_REDUCTION_NEGATIVE_CASE"
    | return
  if selected.isEmpty then return
  let fixtures : Array (String × Name × Array Name × ObviousCertificate × String) := #[
    ("kappa", ``squareVia, #[``squareFact], .lookup ``Nat.exists_mul_self, "searchKappa"),
    ("G", ``squareVia, #[``squareFact], .lookup ``Nat.exists_mul_self, "coveragePrefixG"),
    ("G-control", ``squareVia, #[``squareFact], .lookup ``Nat.exists_mul_self, "positive-control"),
    ("packed", ``sqrtTarget, #[``packed], .lookup ``Nat.sqrt_eq, "reverse-kappa-or-G"),
    ("bounds", ``sqrtTarget, #[``bounds], .lookup ``Nat.sqrt_eq, "reverse-kappa-or-G"),
    ("iff", ``sqrtTarget, #[``reverseIff], .lookup ``Nat.sqrt_eq, "reverse-kappa-or-G"),
    ("split", ``sqrtTarget, #[``lower, ``upper], .lookup ``Nat.sqrt_eq, "reverse-kappa-or-G"),
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
      let checked ← replayCertificate type [] label (some {
        environment := labelBase, disk? := some index,
        implicationModules? := some labelBase.header.moduleNames})
      unless checked.cost == .zero && checked.proof?.isSome do
        throwError "B-only label certificate failed: {selected}: {checked.detail}"
      checkLocalProof type checked.proof?.get!
  let request : Request := {
    target, additions,
    «baseline» := if selected == "unwrapped" then #[] else #[`Mathlib.Data.Nat.Sqrt],
    baselineCommit := basis,
    certificates := if selected == "G-control" then #[⟨label, "G-trap-control"⟩] else #[]}
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
  let reached := match selected with
    | "kappa" => kappa
    | "G" => coverage
    | "packed" | "bounds" | "iff" | "split" => kappa || coverage
    | _ => disposition == .bindOnly
  if selected == "G" then
    if disposition == .reductionR && !budgetBasis reading then
      throwError "G trap produced an exhaustive reduction"
  else if disposition == .reductionR then
    throwError "negative calibration produced a reduction: {selected}"
  if selected == "G-control" || selected == "expensive" then
    unless disposition == .bindOnly do throwError "positive label control did not erase gain: {selected}"
  if selected == "unwrapped" then
    unless reading.baseline.lower == .finite 0 && reading.baseline.upper == .finite 0 &&
        reading.paired.lower == .finite 0 && reading.paired.upper == .finite 0 do
      throwError "unwrapped lost its [0,0]/[0,0] intervals"
  logInfo s!"PRODUCTION_NEGATIVE {Json.mkObj [
    ("case", toJson selected), ("target", toJson target.toString),
    ("label_certificate", toJson label.render), ("label_B_only_kernel_checked", toJson true),
    ("intended_stop", toJson intendedStop), ("targeted_stop_covered", toJson reached),
    ("coverage_gap", toJson (!reached)), ("encountered_search_kappa", toJson kappa),
    ("encountered_coverage_prefix_G", toJson coverage),
    ("A1", toJson (reprStr a1)), ("B", toJson (reprStr disposition)),
    ("pool_control", toJson (selected == "G-control")),
    ("structure_checked", toJson reading.structureChecked),
    ("structure_clean", toJson reading.structureClean),
    ("index_digest", toJson index.header.digest), ("index_inputs", toJson index.header.inputs),
    ("stop_coverage_scope", toJson "same-key slow-before-easy and easy-beyond-G remain unverified unless actual candidate telemetry establishes their positions")
    ] |>.compress}"
