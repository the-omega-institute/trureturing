import D5.S3.ConceptDynamics.InformationEscape.InformationRoot
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow

open Lean LeanInformationAudit LeanInformationAudit.RegistrationGates

-- Completed eleven-query profile on Lean 4.33.0 (2026-09-13). These are
-- independent regression ceilings, not multiples of the production fuel cap.
private def rootWorkProfile : ProvenanceCounters := {
  summarisedConstants := 319, visits := 25486, chargedVisits := 5595485
  recheckedNodes := 571586, spineArguments := 25918, canonicalizations := 1048077
  constructionWork := 225614, traversalWork := 3665438, dispatchWork := 58852 }

-- policy-override: 25% headroom permits implementation changes while detecting
-- repeated-work regressions. Round upward, including for small categories.
private def withinProfile (observed reference : Nat) : Bool :=
  observed <= (5 * reference + 3) / 4

-- Re-run the root's actual registration inputs in a fresh compilation. The
-- memo and counters must not have been imported from InformationRoot's olean.
run_cmd Elab.Command.liftCoreM do
  let initial ← getProvenanceCounters
  unless initial.visits == 0 && initial.summarisedConstants == 0 && initial.memoHits == 0 do
    throwError "[FAIL] CompilationLocalMemo: imported counters"
  let root := `D5.S3.ConceptDynamics.InformationEscape.InformationRoot
  let entries := (InformationRegistry.entries (← getEnv)).filter (·.registrationModuleName == root)
  unless entries.size == 11 do throwError "[FAIL] InformationRootCountBudget: wrong registration count"
  let mut total : ProvenanceCounters := {}
  let firstTrace := (← getTraces).size
  let mut accepted := true
  for entry in entries do
    let actual ← withOptions (·.set `trace.InformationProvenance.check true) <|
      provenanceErrorCurrent root entry.effectiveCatalogId entry.theoremName entry.realizationName
    if let some message := actual then
      accepted := false
      logError m!"[FAIL] InformationRootCountBudget: {message}"
    let counts ← getProvenanceCounters
    if total.visits == 0 && counts.summarisedConstants == 0 then
      throwError "[FAIL] CompilationLocalMemo: imported summaries"
    total := {
      summarisedConstants := total.summarisedConstants + counts.summarisedConstants
      visits := total.visits + counts.visits
      memoHits := total.memoHits + counts.memoHits
      chargedVisits := total.chargedVisits + counts.chargedVisits
      recheckedNodes := total.recheckedNodes + counts.recheckedNodes
      spineArguments := total.spineArguments + counts.spineArguments
      canonicalizations := total.canonicalizations + counts.canonicalizations
      constructionWork := total.constructionWork + counts.constructionWork
      traversalWork := total.traversalWork + counts.traversalWork
      dispatchWork := total.dispatchWork + counts.dispatchWork }
    logInfo m!"InformationRootCounters theorem={entry.theoremName} P_constants_summarised={counts.summarisedConstants} visits={counts.visits} memo_hits={counts.memoHits} charged_visits={counts.chargedVisits}"
  -- Independent registrations need not share executable constants after proof
  -- erasure. Repeated-query reuse is required by ProvenanceMemoWorkAccounting.
  logInfo m!"InformationRootCounters total registrations={entries.size} P_constants_summarised={total.summarisedConstants} visits={total.visits} memo_hits={total.memoHits} charged_visits={total.chargedVisits} rechecked_nodes={total.recheckedNodes} spine_arguments={total.spineArguments} canonicalizations={total.canonicalizations} construction_work={total.constructionWork} traversal_work={total.traversalWork} dispatch_work={total.dispatchWork}"
  unless total.visits >= entries.size &&
      withinProfile total.summarisedConstants rootWorkProfile.summarisedConstants &&
      withinProfile total.visits rootWorkProfile.visits &&
      withinProfile total.chargedVisits rootWorkProfile.chargedVisits &&
      withinProfile total.recheckedNodes rootWorkProfile.recheckedNodes &&
      withinProfile total.spineArguments rootWorkProfile.spineArguments &&
      withinProfile total.canonicalizations rootWorkProfile.canonicalizations &&
      withinProfile total.constructionWork rootWorkProfile.constructionWork &&
      withinProfile total.traversalWork rootWorkProfile.traversalWork &&
      withinProfile total.dispatchWork rootWorkProfile.dispatchWork do
    throwError "[FAIL] InformationRootCountBudget: {repr total}"
  let mut emissions : Nat := 0
  for entry in (← getTraces).toArray[firstTrace:] do
    if (← entry.msg.toString).contains "P_constants_summarised=" then
      emissions := emissions + 1
  unless emissions == entries.size do
    throwError "[FAIL] ProvenanceTraceCounters: {emissions} != {entries.size}"
  unless accepted do return
  logInfo "[PASS] InformationRootCountBudget"
  logInfo "[PASS] ProvenanceTraceCounters"
  logInfo "[PASS] CompilationLocalMemo"

-- Reusing syntax still performs statement-dependent folds and decision work.
-- Require measured work on a warmed query, not just a count of memo misses.
run_cmd Elab.Command.liftCoreM do
  let root := `D5.S3.ConceptDynamics.InformationEscape.InformationRoot
  let some entry := (InformationRegistry.entries (← getEnv)).find?
      (·.registrationModuleName == root) | throwError "missing root registration"
  let firstTrace := (← getTraces).size
  let _ ← withOptions (·.set `trace.InformationProvenance.check true) <|
    provenanceErrorCurrent root entry.effectiveCatalogId entry.theoremName entry.realizationName
  let counts ← getProvenanceCounters
  let mut accounted := false
  for trace in (← getTraces).toArray[firstTrace:] do
    let message ← trace.msg.toString
    let count (key : String) : Nat :=
      if message.contains s!"{key}=" then
        (((message.splitOn s!"{key}=").getLast!).splitOn " ").head!.toNat?.getD 0
      else 0
    if count "rechecked_nodes" > 0 && count "spine_arguments" > 0 &&
        count "canonicalizations" > 0 then accounted := true
  -- The fuel-derived total is independent of the category counter updates.
  let total := counts.constructionWork + counts.recheckedNodes + counts.spineArguments +
    counts.canonicalizations + counts.traversalWork + counts.dispatchWork
  if counts.memoHits > 0 && counts.summarisedConstants == 0 && accounted &&
      counts.constructionWork > 0 && counts.traversalWork > 0 && counts.dispatchWork > 0 &&
      counts.chargedVisits == total then
    logInfo "[PASS] ProvenanceMemoWorkAccounting"
  else
    logError m!"[FAIL] ProvenanceMemoWorkAccounting: fuel and total work differ: {repr counts}"
  let enough ← withOptions (·.set `provenanceExpressionLimit total) <|
    provenanceErrorCurrent root entry.effectiveCatalogId entry.theoremName entry.realizationName
  let exhausted ← withOptions (·.set `provenanceExpressionLimit (total - 1)) <|
    provenanceErrorCurrent root entry.effectiveCatalogId entry.theoremName entry.realizationName
  if enough.isNone && exhausted.any (·.startsWith "IE-C050 ClosedTruthReadout ") then
    logInfo "[PASS] ProvenanceWorkFuelBoundary"
  else
    logError m!"[FAIL] ProvenanceWorkFuelBoundary: exact={enough}, below={exhausted}, fuel={total}"

-- This dependent output family is larger than every InformationRoot query.
-- Check the actual registration so a cap derived from only the smaller root
-- cannot silently publish an IE-C050 diagnostic for this accepted readout.
run_cmd Elab.Command.liftCoreM do
  let root := `D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
  let theoremName :=
    `D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points
  let some entry := (InformationRegistry.entries (← getEnv)).find?
      (fun entry => entry.registrationModuleName == root && entry.theoremName == theoremName)
    | throwError "[FAIL] TemplateShadowReadoutBudget: missing registration"
  let actual ← withOptions (·.set `trace.InformationProvenance.check true) <|
    provenanceErrorCurrent root entry.effectiveCatalogId theoremName entry.realizationName
  if actual.isSome then
    throwError "[FAIL] TemplateShadowReadoutBudget: {actual}"
  logInfo "[PASS] TemplateShadowReadoutBudget"
