import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.LookupBaseline

/-! Recall, nonrecursive closure and incomplete-basis regression checks. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction.LookupBaseline
set_option Elab.async false
set_option maxHeartbeats 0

run_cmd do
  let name := `PlaceholderFixture.member
  let constant : ConstantVal := {name, levelParams := [], type := mkConst ``True}
  let placeholder : ConstantInfo := .axiomInfo {constant with isUnsafe := false}
  let theoremInfo : ConstantInfo := .thmInfo {constant with value := mkConst ``True.intro}
  let unsafeInfo : ConstantInfo := .defnInfo {
    constant with value := mkConst ``True.intro, hints := .opaque, safety := .unsafe}
  let other : ConstantInfo := .thmInfo {
    constant with name := `PlaceholderFixture.other, value := mkConst ``True.intro}
  let parts := #[#[placeholder, other], #[placeholder, unsafeInfo], #[theoremInfo, theoremInfo]]
  let entries := DiskLookup.membershipEntries "Fixture" parts
  unless entries.size == 2 && entries[0]!.leanName == other.name &&
      entries[0]!.ordinal == 2 && entries[1]!.leanName == name && entries[1]!.ordinal == 1 do
    throwError "placeholder/unsafe copy shadowed the safe theorem or changed declaration ordinals"
  unless (DiskLookup.membershipEntries "Fixture" #[#[placeholder, unsafeInfo]]).isEmpty do
    throwError "ineligible copies entered membership"
  let owners := entries ++ DiskLookup.membershipEntries "OtherOwner" parts
  unless owners.size == 4 && owners[1]!.module != owners[3]!.module do
    throwError "distinct membership owners were collapsed"
  logInfo "LOOKUP_MEMBERSHIP synthetic_placeholder=true unsafe_shadow=true dedup=true ordinals=true owners=true"

run_cmd do
  let directory : System.FilePath :=
    "build/lean-inspector/lookup-index/placeholder-fixture"
  let storage := directory / "members"
  IO.FS.createDirAll storage
  let plan := directory / "plan.json"
  let resultPath := directory / "result.json"
  IO.FS.writeFile plan (toJson ({modules := #["Std.Data.ExtDTreeMap.Basic"]} :
    DiskLookup.ShardPlan)).compress
  DiskLookup.produceMembershipShard storage plan resultPath
  let result : DiskLookup.MembershipShardResult ← IO.ofExcept <|
    fromJson? (← IO.ofExcept <| Json.parse (← IO.FS.readFile resultPath))
  unless result.missing.isEmpty do throwError "placeholder fixture indexing incomplete"
  liftTermElabM do
    let env := (← getEnv).setExporting false
    let header : DiskLookup.Header := {
      basis := "placeholder-fixture", mathlib := "fixture", inputs := 0,
      storage := "implication", root := "", digest := 0, complete := true,
      modules := 1, declarations := result.indexed, indexed := result.indexed, missing := #[]}
    let index : DiskLookup.Index := {
      directory := directory / "implication", header, manifest := #[],
      membership? := some {
        inputs := 0, storage := "members", complete := true,
        indexed := result.indexed}}
    withEnv env do
      for name in #[`Std.ExtDTreeMap.getEntryLE._proof_1, `Std.ExtDTreeMap.getEntryGE._proof_1] do
        let info ← getConstInfo name
        unless DiskLookup.membershipEligible info do throwError "fixture theorem is ineligible"
        checkLocalProof info.type (mkConst name (info.levelParams.map Level.param))
        let hits ← DiskLookup.queryMembership index info.type
        unless hits.complete && hits.entries.any (·.leanName == name) do
          throwError "complete membership omitted placeholder-shadowed theorem {name}"
        let root ← mkFreshExprMVar info.type
        let trace ← lookupExact {environment := env, disk? := some index} root.mvarId!
        unless trace.complete && trace.source?.isSome && (← root.mvarId!.isAssigned) do
          throwError "production exact lookup lost placeholder-shadowed theorem {name}"
        checkLocalProof info.type (← instantiateMVars root)
        logInfo "LOOKUP_MEMBERSHIP placeholder_shadow=true exact_hit=true kernel=true std3=true"

run_cmd liftTermElabM do
  let left ← Term.elabType (← `(∀ renamed : Nat, Mark renamed ∧ Side))
  let right ← Term.elabType (← `(∀ {n : Nat}, (let x := n; Mark x) ∧ Side))
  Term.synthesizeSyntheticMVarsNoPostponing
  let left ← instantiateMVars left
  let right ← instantiateMVars right
  unless (← DiskLookup.membershipKey left) == (← DiskLookup.membershipKey right) do
    throwError "membership lost alpha/beta/zeta or binder-annotation invariance"
  let index ← DiskLookup.openIndex
    "build/lean-inspector/lookup-index/lookup-fixture" "lookup-fixture"
    "56a005855ea17e0b0958f73ec801ae140b0a1679"
  let hits ← DiskLookup.queryMembership index left
  unless hits.complete && hits.entries.any (·.leanName == ``pair) do
    throwError "membership failed to recall the complete renamed statement"
  let some header := index.membership? | throwError "membership header missing"
  let key ← DiskLookup.membershipKey left
  let file := index.directory.parent.getD index.directory / header.storage /
    s!"members-{key.toNat % 256}.pickle"
  let withheld := file.addExtension "withheld"
  IO.FS.rename file withheld
  let missing ← try DiskLookup.queryMembership index left
    finally IO.FS.rename withheld file
  unless !missing.complete do throwError "missing membership bucket certified NoHit"
  let absent ← DiskLookup.queryMembership {index with membership? := none} left
  unless !absent.complete do throwError "missing membership header certified NoHit"
  let privateType ← Term.elabType (← `(∀ n : Nat, PrivateMark n))
  Term.synthesizeSyntheticMVarsNoPostponing
  let privateType ← instantiateMVars privateType
  let privateHits ← DiskLookup.queryMembership index privateType
  let privateEntry := privateHits.entries.find? (·.name.endsWith ".hiddenMember")
  unless privateHits.complete && privateEntry.isSome do
    throwError "complete membership omitted a private theorem"
  let privateInfo ← getConstInfo privateEntry.get!.leanName
  unless DiskLookup.membershipEligible privateInfo &&
      LazyDiscrTree.blacklistInsertion (← getEnv) privateInfo.name do
    throwError "private regression no longer distinguishes membership from suggestions"
  logInfo "LOOKUP_MEMBERSHIP private=true suggestion_blacklist_ignored=true"
  logInfo "LOOKUP_MEMBERSHIP alpha=true normalized=true missing_bucket=unknown missing_header=unknown"

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
    let positive ← Term.elabType (← `(∀ n : Nat, Mark n ∧ Side))
    let negative ← Term.elabType (← `(Mark 9))
    Term.synthesizeSyntheticMVarsNoPostponing
    for (type, expected) in #[(← instantiateMVars positive, EdgeCost.zero),
        (← instantiateMVars negative, EdgeCost.one)] do
      withEnv base do
        let type ← copyStatement source .anonymous type
        for _ in [:2] do
          let result ← localRebuild type [] (some table)
          unless result.cost == expected do
            throwError "cold candidate certification: {result.detail}"
          if expected == .one then
            unless result.lookup.complete && result.lookup.unloaded == 0 do
              throwError "external implication was loaded or exclusion became incomplete"
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

run_cmd liftTermElabM do
  let budget ← IO.mkRef ({} : LookupBudgetState)
  let prepared ← boundedRebuildBranch (do
    withLookupPreparation (some budget) do
      IO.addHeartbeats (localBudget * 1000 + 1)
    checkSystem "lookup.search_after_preparation"
    return {cost := .one}) (some budget)
  unless prepared.cost == .one && (← budget.get).preparation > localBudget * 1000 do
    throwError "preparation was charged to search"
  let exceeded ← boundedRebuildBranch (do
    withLookupPreparation (some budget) do
      IO.addHeartbeats (lookupPreparationBudget * 1000 + 1)
      checkSystem "lookup.preparation_overflow"
    return {cost := .one}) (some budget)
  unless exceeded.cost == .unknown && exceeded.detail == "preparation-heartbeat" do
    throwError "preparation overflow became NoHit or escaped its branch: {exceeded.detail}"
  logInfo "LOOKUP_SPLIT_BUDGET preparation_excluded=true preparation_overflow=unknown"

run_cmd do
  enableInitializersExecution
  let imports : Array Import := #[{module := `Lean}]
  let (base, shared) ← withImporting do
    let (_, state) ← (importModulesCore imports).run default
    let base ← finalizeImport state imports {} 0 (leakEnv := false) (loadExts := true)
    pure (base, state)
  liftTermElabM do
    let source ← getEnv
    let index ← DiskLookup.openIndex "build/lean-inspector/lookup-index/lookup-fixture"
      "lookup-fixture" "56a005855ea17e0b0958f73ec801ae140b0a1679"
    let cases ← #[("membership", ← `(∀ n : Nat, Mark n ∧ Side)), ("nonrecursive", ← `(First → Last))].mapM fun (name, stx) => do
      let type ← Term.elabType stx
      Term.synthesizeSyntheticMVarsNoPostponing
      return (name, ← instantiateMVars type)
    let mut expected : Std.HashMap String String := {}
    for pass in [:4] do
      let table ← onDemandLookup {environment := base, disk? := some index} (some shared)
      for (name, type) in (if pass % 2 == 0 then cases else cases.reverse) do
        let bytes ← withEnv base do
          let type ← copyStatement source .anonymous type
          let graph : ProofGraph := {
            root := 0, vertices := [{id := 0, type}],
            edges := [{conclusion := 0}], complete := true}
          let reading ← evaluateGraph graph (some table)
          let baselineProof? ← assembleZero reading.graph
          let pairedProof? ← assembleZero reading.graph true
          let reading := {reading with
            baselineProof?, pairedProof?,
            isolated := true, structureChecked := true,
            structureClean := true, presentationComplete := true}
          if name == "membership" then
            unless reading.baseline == ⟨.finite 0, .finite 0⟩ &&
                reading.baselineProof?.isSome do
              throwError "external membership determinism case did not certify a positive hit"
          let observation : Observation := {
            target := name.toName, graph? := some reading,
            verdict := classifyGraph reading, base := reading.baselineProbe.outcome,
            paired := reading.pairedProbe.outcome}
          return (observationJson observation).compress
        if let some previous := expected[name]? then
          unless bytes.toUTF8 == previous.toUTF8 do
            throwError "cold/warm forward/reverse byte mismatch: {name} pass={pass}"
        else expected := expected.insert name bytes
        IO.eprintln s!"LOOKUP_DETERMINISM case={name} pass={pass} bytes={bytes}"
    logInfo "LOOKUP_DETERMINISM_ACCEPTED cold_warm=true forward_reverse=true per_query_json_bytes=true cases=2 passes=4"

run_cmd liftTermElabM do
  let budget ← IO.mkRef ({} : LookupBudgetState)
  let table : LookupTable := {environment := ← getEnv, budget? := some budget}
  let goal := (← mkFreshExprMVar (mkConst ``True)).mvarId!
  let entry : DiskLookup.Entry := {module := "Fixture", name := "capped", parts := #[]}
  let capped ← boundedLookupCandidate table entry goal do
    IO.addHeartbeats (lookupCandidateBudget * 1000 + 1)
    checkSystem "lookup.candidate.cap-fixture"
    return {complete := true}
  unless !capped.complete && capped.capped.size == 1 do
    throwError "cap became normal failure"
  let failed ← boundedLookupCandidate table {entry with name := "unsupported"} goal do
    throwError "lookup.view_depth_incomplete"
  unless !failed.complete && failed.failures.size == 1 do
    throwError "candidate exception escaped or disappeared"
  let prepared ← boundedLookupCandidate table {entry with name := "preparation"} goal do
    withLookupPreparation (some budget) do
      IO.addHeartbeats (lookupPreparationBudget * 1000 + 1)
      checkSystem "lookup.preparation.cap-fixture"
    return {complete := true}
  unless !prepared.complete && prepared.capped.size == 1 do
    throwError "preparation cap became normal failure"
  let recovered ← boundedLookupCandidate table {entry with name := "recovered"} goal do
    unless !(← goal.isAssigned) do throwError "failed state survived"
    goal.assign (mkConst ``True.intro)
    return {complete := true, source? := some ``True.intro}
  unless recovered.complete && recovered.source?.isSome do
    throwError "earlier failure starved a later checked candidate"
  logInfo "LOOKUP_V7_REGRESSION cap=unknown exception=local preparation=unknown later_candidate=checked"
