import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.LookupBaseline

/-! Recall, nonrecursive closure and incomplete-basis regression checks. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction.LookupBaseline
set_option Elab.async false
set_option maxHeartbeats 0

run_cmd do
  enableInitializersExecution
  let base ← importModules #[{module :=
    `LeanInformationAuditRegTests.SearchReduction.LookupBaseline}] {} 0
    (leakEnv := false) (loadExts := true)
  liftTermElabM do
    let index ← DiskLookup.openIndex
      "build/lean-inspector/lookup-index/lookup-fixture" "lookup-fixture"
      "56a005855ea17e0b0958f73ec801ae140b0a1679"
    let table : LookupTable := {environment := base, disk? := some index}
    let cases ← #[
      ← `(Mark 9),
      ← `(∀ renamed : Nat, Mark renamed),
      ← `(∀ second first : Nat, Mark first → Combined first second),
      ← `(Left → Right), ← `(Right → Left),
      ← `(InstanceMark 7), ← `(∀ n : Nat, Mark n → Finish),
      ← `(DataMark 11)].mapM fun stx => do
        let type ← Term.elabType stx
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars type
    for h : i in [:cases.size] do
      let result ← localRebuild cases[i] [] (some table)
      unless result.cost == .zero && result.proof?.isSome do
        throwError "lookup recall {i}: {result.detail}"
      logInfo s!"LOOKUP_RECALL index={i} {result.detail}"
    let type ← Term.elabType (← `(First → Last))
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    let result ← localRebuild type [] (some table)
    let unresolvedOwner := result.cost == .unknown &&
      (result.detail.splitOn "candidate-not-loaded").length > 1
    unless result.cost == .one || unresolvedOwner do
      throwError "lookup composed two B declarations: {result.detail}"
    let bucket := hash (DiscrTree.Key.const ``Last 0)
    let files := index.manifest.find? (fun item => item.1 == bucket) |>.map (·.2) |>.getD #[]
    unless !files.isEmpty do throwError "missing Last fixture shard"
    let node := index.directory / files[0]!
    let withheld := node.addExtension "withheld"
    IO.FS.rename node withheld
    let missingPage ← try localRebuild type [] (some table)
      finally IO.FS.rename withheld node
    unless missingPage.cost == .unknown do
      throwError "missing index node became certified NoHit"
    logInfo "LOOKUP_MISSING_PAGE unknown=true"
    let incomplete ← localRebuild type [] (some {table with complete := false})
    unless incomplete.cost == .unknown do
      throwError "partial enumeration became NoHit: {incomplete.detail}"
    let off ← localRebuild type [] (some {table with enabled := false})
    let legacy ← localRebuild type
    unless off.cost == legacy.cost do throwError "lookup ablation changed local closure"
    logInfo s!"LOOKUP_NONRECURSIVE {result.detail}"
    logInfo s!"LOOKUP_INCOMPLETE {incomplete.detail}"
    logInfo "LOOKUP_ABLATION equal=true"
    let finish ← Term.elabType (← `(Finish))
    let mark ← Term.elabType (← `(Mark 2))
    let unused ← Term.elabType (← `(Side))
    Term.synthesizeSyntheticMVarsNoPostponing
    let tail ← localRebuild (← instantiateMVars finish)
      [← instantiateMVars mark, ← instantiateMVars unused] (some table)
    unless tail.cost == .zero && tail.used == [0] do
      throwError "lookup retained an unused premise: {tail.detail}, {tail.used}"
    logInfo "LOOKUP_ACTUAL_TAIL used=[0]"
