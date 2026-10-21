import LeanInformationAuditRegAnalysis.SearchReduction.Isolation
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
    unless result.cost == .one do
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

run_cmd do
  enableInitializersExecution
  let base ← importModules #[{module := `Lean}] {} 0 (loadExts := true)
  liftTermElabM do
    let source ← getEnv
    let index ← DiskLookup.openIndex
      "build/lean-inspector/lookup-index/lookup-fixture" "lookup-fixture"
      "56a005855ea17e0b0958f73ec801ae140b0a1679"
    let table ← onDemandLookup {environment := base, disk? := some index}
    let positive ← Term.elabType (← `(∀ second first : Nat,
      Mark first → Combined first second))
    let negative ← Term.elabType (← `(First → Last))
    Term.synthesizeSyntheticMVarsNoPostponing
    for (type, expected) in #[(← instantiateMVars positive, EdgeCost.zero),
        (← instantiateMVars negative, EdgeCost.one)] do
      withEnv base do
        let type ← copyStatement source .anonymous type
        for _ in [:2] do
          let result ← localRebuild type [] (some table)
          unless result.cost == expected do
            throwError "cold candidate certification: {result.detail}"
          logInfo s!"LOOKUP_COLD cost={reprStr result.cost} {result.detail}"

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
