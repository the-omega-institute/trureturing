import D5.S3.ConceptDynamics.InformationEscape.InformationRoot

open Lean LeanInformationAudit LeanInformationAudit.RegistrationGates

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
  for entry in entries do
    let actual ← withOptions (·.set `trace.InformationProvenance.check true) <|
      provenanceErrorCurrent root entry.effectiveCatalogId entry.theoremName entry.realizationName
    if let some message := actual then
      throwError "[FAIL] InformationRootCountBudget: {message}"
    let counts ← getProvenanceCounters
    if total.visits == 0 && counts.summarisedConstants == 0 then
      throwError "[FAIL] CompilationLocalMemo: imported summaries"
    total := {
      summarisedConstants := total.summarisedConstants + counts.summarisedConstants
      visits := total.visits + counts.visits
      memoHits := total.memoHits + counts.memoHits
      chargedVisits := total.chargedVisits + counts.chargedVisits }
    logInfo m!"InformationRootCounters theorem={entry.theoremName} P_constants_summarised={counts.summarisedConstants} visits={counts.visits} memo_hits={counts.memoHits} charged_visits={counts.chargedVisits}"
  unless total.memoHits > 0 do throwError "[FAIL] InformationRootCountBudget: no summary reuse"
  logInfo m!"InformationRootCounters total registrations={entries.size} P_constants_summarised={total.summarisedConstants} visits={total.visits} memo_hits={total.memoHits} charged_visits={total.chargedVisits}"
  -- Fixed bounds above the measured 319 summaries / 23279 syntax visits.
  -- They are independent of production fuel constants and of wall time.
  unless total.summarisedConstants <= 384 && total.visits <= 28000 &&
      total.visits >= entries.size && total.chargedVisits <= 23000 do
    throwError "[FAIL] InformationRootCountBudget: {repr total}"
  let mut emissions : Nat := 0
  for entry in (← getTraces).toArray[firstTrace:] do
    if (← entry.msg.toString).contains "P_constants_summarised=" then
      emissions := emissions + 1
  unless emissions == entries.size do
    throwError "[FAIL] ProvenanceTraceCounters: {emissions} != {entries.size}"
  logInfo "[PASS] InformationRootCountBudget"
  logInfo "[PASS] ProvenanceTraceCounters"
  logInfo "[PASS] CompilationLocalMemo"
