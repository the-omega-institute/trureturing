import LeanInformationAuditRegAnalysis.SearchReduction.Commands

/-! Published blockers identify the operation that actually prevents completion. -/
open Lean Elab Command LeanInformationAudit.SearchReduction
set_option Elab.async false

private def reading (terminal : RQuery) (detail : String) : GraphReading := {
  graph := {vertices := [
    {id := 350, seed := true},
    {id := 791, structureSeed := true, independentLookup := .exhausted,
      independentLookupDetail := "normal-exhaustion", reverseLookupDetail := detail}]},
  selectedSeeds := [350, 791], targetPartComplete := false,
  isolated := true, presentationComplete := true, structureChecked := true, structureClean := true,
  «baseline» := ⟨.finite 2, .finite 4⟩, paired := ⟨.finite 0, .finite 1⟩,
  queryRecords := [{role := "target-part-reverse:791", target := 123, premises := [456], terminal}]}

private def observation (g : GraphReading) : Observation := {
  target := `BlockerTarget, base := .exhausted, paired := .incomplete .undecided,
  verdict := .insufficient, graph? := some g}

run_cmd do
  for (terminal, detail, expected) in [
      (RQuery.miss .searchKappa, "lookup-incomplete-basis", "searchKappa"),
      (RQuery.notRun, "unclosed-reconstruction", "unclosed-reconstruction")] do
    let g := reading terminal detail
    let j := observationJson (observation g)
    let blocker ← ofExcept (j.getObjVal? "blocker")
    let pair ← ofExcept (blocker.getObjValAs? String "query_or_check_pair")
    let stop ← ofExcept (blocker.getObjValAs? String "stop")
    unless pair == "BlockerTarget:seed:791;query=target-part-reverse:791:123" &&
        (stop.splitOn expected).length > 1 && (stop.splitOn "not-queried").length == 1 &&
        classifyDisposition g == .incomplete &&
        g.baseline == ⟨.finite 2, .finite 4⟩ && g.paired == ⟨.finite 0, .finite 1⟩ do
      throwError "BLOCKER actual unfinished query or unchanged intervals lost: {blocker}"
  let g := {reading .notRun "not-queried" with
    structureChecked := false, structureClean := false, noAuxiliary := true}
  let blocker ← ofExcept ((observationJson (observation g)).getObjVal? "blocker")
  let stop ← ofExcept (blocker.getObjValAs? String "stop")
  unless (← ofExcept (blocker.getObjValAs? String "guard")) == "wide-S-and-source-isolation" &&
      stop == "NotRun: no auxiliary structure supplied; paired reconstruction not scheduled" do
    throwError "BLOCKER empty structural stop was not identified: {blocker}"
  logInfo "BLOCKER PASS executed-kappa actual-seed notRun nonempty-structural-stop intervals-preserved"
