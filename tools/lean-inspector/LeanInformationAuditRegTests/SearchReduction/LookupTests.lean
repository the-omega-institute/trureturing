import LeanInformationAuditRegAnalysis.SearchReduction.Isolation
import LeanInformationAuditRegTests.SearchReduction.LookupBaseline

/-! Recall, nonrecursive closure and incomplete-basis regression checks. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction.LookupBaseline
set_option Elab.async false
set_option maxHeartbeats 0

run_cmd do
  let parameter := mkBVar 0
  let nested := mkApp2 (mkConst ``And) (mkConst ``True) parameter
  let first := DiskLookup.path (fun _ => true) (mkApp2 (mkConst ``And) nested parameter)
  let second := DiskLookup.path (fun _ => true) (mkApp2 (mkConst ``And) (mkConst ``False) parameter)
  unless first != second && first.length > 3 do
    throwError "candidate keys lost nested application structure"
  let bound := DiskLookup.path (fun _ => true)
    (.lam `renamed (mkConst ``Nat) (mkApp2 (mkConst ``And) parameter parameter) .default)
  unless bound.head? == some "l:1" && bound.contains "*" do
    throwError "candidate keys lost binder position or parameter wildcard"
  let eta := .lam `x (mkConst ``Nat) (mkApp (mkBVar 1) (mkBVar 0)) .default
  unless DiskLookup.path (fun _ => true) eta == DiskLookup.path (fun _ => true) parameter do
    throwError "candidate key is not eta invariant"
  logInfo s!"LOOKUP_KEY_SHAPE nested=true binders=true parameters=true \
    eta=true depth={DiskLookup.keyDepth}"

run_cmd do
  let directory : System.FilePath := "build/lean-inspector/lookup-index/ordered-key-fixture"
  IO.FS.createDirAll directory
  let leaf := fun (label : String) (ordinal : Nat) => do
    let entry : DiskLookup.Entry := {
      module := "fixture"
      name := s!"candidate{ordinal}"
      parts := #[(s!"candidate{ordinal}", 0)]
      ordinal := ordinal
      route := "c:1:Target"}
    let payload := (toJson #[entry]).compress
    IO.FS.writeFile (directory / s!"{label}.entries.json") payload
    let node : DiskLookup.Node := {pages := #[{
      file := s!"{label}.entries.json", digest := hash payload, count := 1}]}
    let text := (toJson node).compress
    IO.FS.writeFile (directory / s!"{label}.node.json") text
    pure (hash text)
  let a ← leaf "a" 2
  let z ← leaf "z" 1
  let node : DiskLookup.Node := {children := #[("c:0:A", "a", a), ("c:0:Z", "z", z)]}
  let text := (toJson node).compress
  IO.FS.writeFile (directory / "root.node.json") text
  let header : DiskLookup.Header := {
    basis := "order-fixture"
    mathlib := "fixture"
    inputs := 0
    storage := ""
    root := "root"
    digest := hash text
    complete := true
    modules := 1
    declarations := 2
    indexed := 2
    missing := #[]}
  let result ← DiskLookup.query {directory, header} ["*"]
  unless result.complete && result.entries.map (·.name) == #["candidate1", "candidate2"] do
    throwError "nested key traversal changed the frozen candidate order"
  logInfo "LOOKUP_CANDIDATE_ORDER nested_traversal_reversed=true legacy_order_preserved=true"

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
    let node := index.directory / s!"{index.header.root}.node.json"
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
  let a ← Term.elabType (← `(∀ left : Nat, left = left))
  let b ← Term.elabType (← `(∀ renamed : Nat, renamed = renamed))
  Term.synthesizeSyntheticMVarsNoPostponing
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  unless (DiskLookup.canonical a).hash == (DiskLookup.canonical b).hash do
    throwError "disk member key is not alpha invariant"
  logInfo "LOOKUP_ALPHA_HASH equal=true"

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

run_cmd liftTermElabM do
  let mut shared := mkConst ``True
  for _ in [:24] do shared := mkApp2 (mkConst ``And) shared shared
  unless (DiskLookup.canonical shared).hash == shared.hash do
    throwError "shared statement normalization changed its shape"
  logInfo "LOOKUP_SHARED_NORMALIZATION dag_depth=24 equal=true"

run_cmd do
  let directory : System.FilePath := "build/lean-inspector/lookup-index/packed-record-fixture"
  IO.FS.createDirAll directory
  let entry : DiskLookup.Entry := {module := "fixture", name := "packedFixture", parts := #[("packedFixture", 0)]}
  let payload := (toJson (#[entry] : Array DiskLookup.Entry)).compress
  let leaf : DiskLookup.Node := {pages := #[{file := "records.json#0", digest := hash payload, count := 1}]}
  let text := (toJson leaf).compress
  let records := toJson (#[payload, text] : Array String)
  IO.FS.writeFile (directory / "records.json") records.compress
  IO.FS.writeFile (directory / "root.node.json") text
  let header : DiskLookup.Header := {
    basis := "packed-record-fixture", mathlib := "fixture", inputs := 0, storage := "",
    root := "root", digest := hash text, complete := true, modules := 1,
    declarations := 1, indexed := 1, missing := #[]}
  let index : DiskLookup.Index := {directory, header}
  let found ← DiskLookup.query index []
  unless found.complete && found.entries.map (·.name) == #["packedFixture"] do
    throwError "packed page did not return its checked logical record"
  let packedRoot ← DiskLookup.query {index with header := {header with root := "records.json#1"}} []
  unless packedRoot.complete && packedRoot.entries.map (·.name) == #["packedFixture"] do
    throwError "packed routing node did not return its checked payload"
  IO.FS.writeFile (directory / "records.json") (toJson (#["{}"] : Array String)).compress
  let corrupt ← DiskLookup.query index []
  unless !corrupt.complete && corrupt.entries.isEmpty do
    throwError "corrupt packed record became a certified negative"
  IO.FS.writeFile (directory / "records.json") (toJson (#[] : Array String)).compress
  let missing ← DiskLookup.query index []
  unless !missing.complete && missing.entries.isEmpty do
    throwError "missing packed record became a certified negative"
  IO.FS.writeFile (directory / "records.json") records.compress
  logInfo "LOOKUP_PACKED_RECORD selected=true checksum=true missing=true"

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
