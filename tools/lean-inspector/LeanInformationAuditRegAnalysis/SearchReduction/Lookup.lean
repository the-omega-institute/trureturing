import LeanInformationAuditRegAnalysis.SearchReduction.DiskLookup
import LeanInformationAuditRegAnalysis.SearchReduction.LookupPruning

/-! One-basis-declaration retrieval from checked disk pages. No query scans
the baseline environment or constructs an environment-wide tree. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta

def lookupPhase (label : String) : IO Unit := do
  if let some path ← IO.getEnv "SEARCH_REDUCTION_PROFILE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn s!"{← IO.monoMsNow} {label}"

/-- Resource and residual records are durable even when elaboration is interrupted. -/
def emitLookupRecord (line : String) : IO Unit := do
  lookupPhase line
  IO.eprintln line

/-- Includes exceptional exits; nested spans must not be added to their parent. -/
def timeLookup {α : Type} (label : String) (action : MetaM α) : MetaM α := do
  if (← IO.getEnv "SEARCH_REDUCTION_PROFILE").isNone then return ← action
  let start ← IO.monoNanosNow
  let heartbeats ← IO.getNumHeartbeats
  lookupPhase s!"{label}/start"
  try action finally
    lookupPhase s!"{label}/end ns={(← IO.monoNanosNow) - start} heartbeats={(← IO.getNumHeartbeats) - heartbeats}"

abbrev lookupVersion : String := "R_lookup/v18/obvious-v1/lazy-interval/scope-B_T/primary-index-only/candidate-200000/preparation-8000000/G-340000000/memo-target-basis-R-v2/N-memo-2000000/checkpoint-v5/views-kappa"

abbrev lookupCandidateBudget : Nat := 200000
/-- Frozen from verdict-free fallback and fixed-stride candidate telemetry. -/
abbrev lookupCoverageBudget : Nat := 340000000

/-- Bounded, query-local metadata reuse; certificates are always checked anew. -/
structure LookupQueryMemo where
  primary? : Option (Environment × Std.HashMap Expr DiskLookup.Candidates) := none
  fallback? : Option (Environment × DiskLookup.Index × Option (Array Name) ×
    DiskLookup.Candidates) := none
  profile? : Option (Environment × Array DiskLookup.Entry × Nat × Nat) := none

structure LookupCandidate where
  values : Array Expr := #[]
  certify : MetaM Unit := pure ()
  failure? : Option String := none
  unloaded : Bool := false

/-- The table is captured before delivery vocabulary or S is installed. A
partial basis may supply a hit, but never a completed negative query. -/
structure LookupTable where
  environment : Environment
  implicationModules? : Option (Array Name) := none
  complete : Bool := true
  enabled : Bool := true
  disk? : Option DiskLookup.Index := none
  load? : Option (DiskLookup.Entry → Option Name → Expr → MetaM LookupCandidate) := none
  close? : Option (IO Unit) := none
  finish? : Option (Environment → Expr → MetaM Expr) := none
  memo? : Option (IO.Ref LookupQueryMemo) := none
  budget? : Option (IO.Ref LookupBudgetState) := none
  /-- Speculative loaded candidates have private state and no checkpoint or
  certificate side effects. A possible hit is replayed by the owning thread. -/
  speculative : Bool := false

structure LookupTrace where
  visited : Nat := 0
  attempted : Nat := 0
  pages : Nat := 0
  missing : Array Name := #[]
  failures : Array String := #[]
  unloaded : Nat := 0
  source? : Option Name := none
  complete : Bool := false
  capped : Array String := #[]
  fallbackVisited : Nat := 0
  fallbackTotal : Nat := 0
  deriving Inhabited

private def eligible : ConstantInfo → Bool
  | .thmInfo _ | .defnInfo _ | .opaqueInfo _ => true
  | _ => false

private def candidateOwnerMatches (table : LookupTable) (entry : DiskLookup.Entry) : Bool :=
  match table.environment.getModuleIdxFor? entry.leanName with
  | some idx => table.environment.header.moduleNames[idx.toNat]?.any (fun n => n.toString == entry.module)
  | none => false

private unsafe def profileCandidateSet (table : LookupTable) (type : Expr)
    (candidates : DiskLookup.Candidates) (fallback : Bool) (mode : String) : IO Unit := do
  if (← IO.getEnv "SEARCH_REDUCTION_PROFILE").isNone then return
  let started ← IO.monoNanosNow
  let heartbeats ← IO.getNumHeartbeats
  let cached ← match table.memo? with
    | some memo => (·.profile?) <$> memo.get
    | none => pure none
  let cached := cached.filter fun (env, entries, _, _) =>
    ptrEq env table.environment && ptrEq entries candidates.entries
  let (loaded, modules) ← if let some (_, _, loaded, modules) := cached then
      pure (loaded, modules)
    else do
      let mut loaded := 0
      let mut modules : Std.HashSet String := {}
      for entry in candidates.entries do
        if candidateOwnerMatches table entry then loaded := loaded + 1
        else modules := modules.insert entry.module
      unless candidates.entries.isEmpty do
        if let some memo := table.memo? then
          memo.modify fun state => {state with
            profile? := some (table.environment, candidates.entries, loaded, modules.size)}
      pure (loaded, modules.size)
  lookupPhase s!"lookup/set mode={mode} fallback={fallback} query={type.hash} total={candidates.entries.size} loaded={loaded} unloaded={candidates.entries.size - loaded} unloaded_modules={modules} profile_cached={cached.isSome}"
  lookupPhase s!"lookup/query mode={mode} fallback={fallback} closed={!type.hasMVar && !type.hasFVar} expression={(toJson (reprStr type)).compress}"
  lookupPhase s!"lookup/recall-profile/end ns={(← IO.monoNanosNow) - started} heartbeats={(← IO.getNumHeartbeats) - heartbeats}"

private def candidateValue (table : LookupTable) (entry : DiskLookup.Entry) (head : Option Name) (query : Expr) :
    MetaM LookupCandidate := do
  if let some info := (table.environment.setExporting false).find? entry.leanName |>.filter (fun _ => candidateOwnerMatches table entry) then
    if !eligible info || info.isUnsafe then return {}
    return {values := #[← mkConstWithFreshMVarLevels entry.leanName]}
  let some load := table.load? | return {failure? := some "candidate-not-loaded", unloaded := true}
  try
    let result ← load entry head query
    let collision := (table.environment.setExporting false).contains entry.leanName &&
      !candidateOwnerMatches table entry
    return {result with
      unloaded := true
      failure? := result.failure?.or (if collision then
        some s!"candidate-name-owned-by-another-module:{entry.module}:{entry.name}" else none)}
  catch ex =>
    if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
    return {failure? := some s!"candidate-certification:{← ex.toMessageData.toString}", unloaded := true}

private def tableIndex (table : LookupTable) : IO (Option DiskLookup.Index) := do
  if table.disk?.isSome then return table.disk?
  let directory := (← IO.getEnv "SEARCH_REDUCTION_INDEX").getD
    "build/lean-inspector/lookup-index/fixture"
  try
    return some (← DiskLookup.openIndex directory "fixture"
      "56a005855ea17e0b0958f73ec801ae140b0a1679")
  catch _ => return none

def resolveLookupTable (table : LookupTable) : IO LookupTable := do
  let disk? ← tableIndex table
  return {table with disk?, complete := table.complete && disk?.any (fun index =>
    index.header.complete)}

private unsafe def queryLookup (table : LookupTable) (index : DiskLookup.Index)
    (type : Expr) (limit : Option Nat) (fallback : Bool) : MetaM DiskLookup.Candidates := do
  let environment ← getEnv
  let mut xs := #[]
  for decl in ← getLCtx do xs := xs.push decl.toExpr
  let closedQuery ← mkForallFVars xs (← instantiateMVars type)
  if !fallback && !closedQuery.hasMVar && !closedQuery.hasFVar then
    if let some memo := table.memo? then
      if let some (env, queries) := (← memo.get).primary? then
        if ptrEq env environment then
          if let some candidates := queries[closedQuery]? then
            lookupPhase "lookup/primary-recall cached=true"
            return candidates
  if fallback then
    if let some memo := table.memo? then
      if let some (env, disk, modules, candidates) := (← memo.get).fallback? then
        if ptrEq env table.environment && ptrEq disk index && modules == table.implicationModules? then
          lookupPhase s!"lookup/static-star cached=true retained={candidates.entries.size} pruned={candidates.staticFailures}"
          return candidates
  -- Recompute matching in every reset search branch; only module bytes cache.
  let candidates ← DiskLookup.queryMature index type limit fallback table.budget?
  withLookupPreparation table.budget? do
    let retained := candidates.entries.filter fun entry =>
      candidateOwnerMatches table entry &&
        table.implicationModules?.all (·.contains entry.module.toName)
    lookupPhase s!"lookup/scope=B_T retained={retained.size} excluded={candidates.entries.size - retained.size}"
    let mut entries := #[]
    let mut staticFailures := 0
    for entry in retained do
      let impossible ← if fallback then
          withEnv table.environment do
            if let some info := (table.environment.setExporting false).find? entry.leanName then
              try starCandidateImpossible info.type catch ex => do
                if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
                pure false
            else pure false
        else pure false
      if impossible then staticFailures := staticFailures + 1
      else entries := entries.push entry
    let result := {candidates with entries, staticFailures}
    if !fallback && !closedQuery.hasMVar && !closedQuery.hasFVar then
      if let some memo := table.memo? then
        memo.modify fun state =>
          let queries := match state.primary? with
            | some (env, queries) =>
              if ptrEq env environment && queries.size < 64 then queries else {}
            | none => {}
          {state with primary? := some (environment, queries.insert closedQuery result)}
    if fallback then
      emitLookupRecord s!"LOOKUP_STATIC_STAR {Json.mkObj [
        ("scope", toJson "B_T"), ("before", toJson retained.size),
        ("pruned", toJson staticFailures), ("after", toJson entries.size)] |>.compress}"
      if let some memo := table.memo? then
        memo.modify fun state => {state with
          fallback? := some (table.environment, index, table.implicationModules?, result)}
    return result

/-- Catch resource exceptions below Core's rethrowing exception layer. -/
def catchLookupCandidate {α : Type} (action : MetaM α)
    (handler : Exception → MetaM α) : MetaM α :=
  controlAt CoreM fun runInBase => fun ctx state => do
    try runInBase action ctx state
    catch ex => runInBase (handler ex) ctx state

private def coverageAvailable (table : LookupTable) : MetaM Bool := do
  if lookupCoverageBudget == 0 then return true
  return (← table.budget?.mapM (·.get)).all (·.coverage < lookupCoverageBudget * 1000)

/-- The final certificate is checked in the original query environment, after
all temporary support is inlined. Its locals are exactly the registered Γ. -/
private def checkLookupGoal (table : LookupTable) (base : Environment)
    (goal : MVarId) : MetaM Expr := goal.withContext do
  let proof ← instantiateMVars (mkMVar goal)
  unless !proof.hasMVar do throwError "lookup.unclosed_certificate"
  let mut xs := #[]
  for decl in ← getLCtx do xs := xs.push decl.toExpr
  let proof ← mkLambdaFVars xs proof
  let proof ← if let some finish := table.finish? then finish base proof else pure proof
  let type ← mkForallFVars xs (← goal.getType)
  unless !proof.hasFVar && !proof.hasMVar && !proof.hasSorry && !type.hasMVar do
    throwError "lookup.unclosed_certificate"
  timeLookup "lookup-certificate" do
    withEnv base do
      let name ← mkFreshUserName `_lookupChecked
      let levels := (collectLevelParams {} type).params.toList
      if ← isProp type then
        addDecl (.thmDecl {name, levelParams := levels, type, value := proof})
      else
        addDecl (.defnDecl {
          name, levelParams := levels, type, value := proof,
          hints := .abbrev, safety := .safe})
      let axioms ← collectAxioms name
      unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
        throwError "lookup.nonstandard_axioms"
  emitLookupRecord s!"LOOKUP_CERTIFICATE {Json.mkObj [
    ("support", toJson (proof.getUsedConstants.map Name.toString)),
    ("query_environment_only", toJson true)] |>.compress}"
  return proof

private def mergeLookupTrace (a b : LookupTrace) : LookupTrace := {
  visited := a.visited + b.visited, attempted := a.attempted + b.attempted,
  pages := a.pages + b.pages, missing := a.missing ++ b.missing,
  failures := a.failures ++ b.failures, capped := a.capped ++ b.capped,
  unloaded := a.unloaded + b.unloaded, source? := a.source?.or b.source?,
  complete := a.complete && b.complete,
  fallbackVisited := a.fallbackVisited + b.fallbackVisited,
  fallbackTotal := a.fallbackTotal + b.fallbackTotal}

def ownedLookupName : Name → Name
  | .anonymous => .anonymous
  | .str p s => .str (ownedLookupName p) (String.ofList s.toList)
  | .num p n => .num (ownedLookupName p) (toString n).toNat!

private def ownedLookupLevel : Level → Level
  | .zero => .zero
  | .succ l => .succ (ownedLookupLevel l)
  | .max a b => .max (ownedLookupLevel a) (ownedLookupLevel b)
  | .imax a b => .imax (ownedLookupLevel a) (ownedLookupLevel b)
  | .param n => .param (ownedLookupName n)
  | .mvar n => .mvar ⟨ownedLookupName n.name⟩

/-- Meta's environment-level realization caches can retain names even after
Core/Meta state is restored. Inputs as well as exported results must own their
storage before they enter Meta. -/
private partial def ownedLookupExpr (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
  if let some found := (← get)[e]? then return found
  let result : Expr ← match e with
    | .bvar i => pure (.bvar i)
    | .fvar n => pure (.fvar ⟨ownedLookupName n.name⟩)
    | .mvar n => pure (.mvar ⟨ownedLookupName n.name⟩)
    | .sort l => pure (.sort (ownedLookupLevel l))
    | .const n ls => pure (.const (ownedLookupName n) (ls.map ownedLookupLevel))
    | .app f a => return .app (← ownedLookupExpr f) (← ownedLookupExpr a)
    | .lam n t b bi => do
      return .lam (ownedLookupName n) (← ownedLookupExpr t) (← ownedLookupExpr b) bi
    | .forallE n t b bi => do
      return .forallE (ownedLookupName n) (← ownedLookupExpr t) (← ownedLookupExpr b) bi
    | .letE n t v b nd => do
      let t ← ownedLookupExpr t
      let v ← ownedLookupExpr v
      let b ← ownedLookupExpr b
      return .letE (ownedLookupName n) t v b nd
    | .lit (.natVal n) => pure (.lit (.natVal (toString n).toNat!))
    | .lit (.strVal s) => pure (.lit (.strVal (String.ofList s.toList)))
    | .mdata _ b => ownedLookupExpr b
    | .proj n i b => return .proj (ownedLookupName n) i (← ownedLookupExpr b)
  modify (·.insert e result)
  return result

/-- Detach all expression storage from a temporary import region. -/
def detachLookupExpression (proof : Expr) : Expr :=
  (ownedLookupExpr proof).run' {}

/-- Copy the declaration metadata used by vocabulary reconstruction. No
temporary module pointer may become a kernel declaration or realization key. -/
def detachLookupConstantInfo (info : ConstantInfo) : ConstantInfo := Id.run do
  let val := info.toConstantVal
  let val : ConstantVal := {
    name := ownedLookupName val.name
    levelParams := val.levelParams.map ownedLookupName
    type := detachLookupExpression val.type}
  return match info with
    | .axiomInfo v => .axiomInfo {v with toConstantVal := val}
    | .defnInfo v => .defnInfo {v with
        toConstantVal := val
        value := detachLookupExpression v.value, all := v.all.map ownedLookupName,
        hints := match v.hints with
          | .opaque => .opaque
          | .abbrev => .abbrev
          | .regular height => .regular height}
    | .thmInfo v => .thmInfo {v with
        toConstantVal := val
        value := detachLookupExpression v.value, all := v.all.map ownedLookupName}
    | .opaqueInfo v => .opaqueInfo {v with
        toConstantVal := val
        value := detachLookupExpression v.value, all := v.all.map ownedLookupName}
    | .inductInfo v => .inductInfo {v with
        toConstantVal := val
        all := v.all.map ownedLookupName, ctors := v.ctors.map ownedLookupName}
    | .ctorInfo v => .ctorInfo {v with toConstantVal := val, induct := ownedLookupName v.induct}
    | .recInfo v => .recInfo {v with
        toConstantVal := val
        all := v.all.map ownedLookupName,
        rules := v.rules.map (fun r => {r with
          ctor := ownedLookupName r.ctor
          rhs := detachLookupExpression r.rhs})}
    | .quotInfo v => .quotInfo {v with toConstantVal := val}

/-- A checkpoint is scoped to one exact attempt in one reading, rather than
an answer cache shared by queries. JSON is never read as semantic evidence. -/
structure LookupCheckpoint where
  identity : String
  query : Expr
  entry : DiskLookup.Entry
  trace : LookupTrace
  proof? : Option Expr
  search : Nat
  preparation : Nat

initialize lookupAttemptOrdinal : IO.Ref Nat ← IO.mkRef 0
initialize lookupExternalAttempts : IO.Ref Nat ← IO.mkRef 0
initialize lookupCheckpointIdentity : IO.Ref (Option String) ← IO.mkRef none

private def checkpointIdentity : IO String := do
  if let some identity ← lookupCheckpointIdentity.get then return identity
  let request ← IO.getEnv "SEARCH_REDUCTION_REQUESTS"
  let requestBytes ← request.mapM IO.FS.readFile
  let identity := reprStr (lookupVersion, request, requestBytes,
    ← IO.getEnv "SEARCH_REDUCTION_SOURCE_LIBRARY", ← IO.getEnv "SEARCH_REDUCTION_RESUME_INPUTS")
  lookupCheckpointIdentity.set (some identity)
  return identity

private def ownedCheckpointTrace (t : LookupTrace) : LookupTrace :=
  {t with
    missing := t.missing.foldl (fun out n => out.push (ownedLookupName n)) #[],
    failures := t.failures.foldl (fun out s => out.push (String.ofList s.toList)) #[],
    capped := t.capped.foldl (fun out s => out.push (String.ofList s.toList)) #[],
    source? := t.source?.map ownedLookupName}

/-- Checkpoint regions live until process exit. Expression sharing can retain
mapped query storage even when returned expressions are reconstructed. -/
initialize lookupCheckpointRegions : IO.Ref (Array CompactedRegion) ← IO.mkRef #[]

private unsafe def readLookupCheckpoint (path : System.FilePath) : IO LookupCheckpoint := do
  let (r, region) ← unpickle LookupCheckpoint path
  lookupCheckpointRegions.modify (·.push region)
  let result : LookupCheckpoint := {r with
    identity := String.ofList r.identity.toList,
    query := detachLookupExpression r.query,
    entry := {r.entry with
      module := String.ofList r.entry.module.toList, name := String.ofList r.entry.name.toList,
      route := String.ofList r.entry.route.toList,
      parts := r.entry.parts.foldl (fun out (s,n) => out.push (String.ofList s.toList,n)) #[]},
    trace := ownedCheckpointTrace r.trace,
    proof? := r.proof?.map detachLookupExpression}
  return result

/-- Every attempt starts from the same branch state and receives its own κ.
An exceptional candidate contributes unknown and never stops its successors. -/
unsafe def boundedLookupCandidate (table : LookupTable) (entry : DiskLookup.Entry)
    (goal : MVarId) (action : MetaM LookupTrace) : MetaM LookupTrace := do
  if (← IO.getEnv "SEARCH_REDUCTION_PREPARATION_TELEMETRY").isSome then
    throwError "lookup.preparation_telemetry_cannot_judge"
  let ordinal ← if table.speculative then pure 0 else lookupAttemptOrdinal.get
  unless table.speculative do lookupAttemptOrdinal.modify (· + 1)
  let configuredResume ← IO.getEnv "SEARCH_REDUCTION_RESUME"
  let resume? := if table.speculative then none else configuredResume.filter (!·.isEmpty)
  let mut xs := #[]
  for decl in ← getLCtx do xs := xs.push decl.toExpr
  let query ← mkForallFVars xs (← instantiateMVars (← goal.getType))
  let checkpoint? := resume?.map fun directory =>
    (System.FilePath.mk directory) / s!"candidate-{ordinal}.pickle"
  let startedReplay ← IO.getNumHeartbeats
  if let some path := checkpoint? then
    if ← path.pathExists then
      let record ← readLookupCheckpoint path
      if record.identity == ((← checkpointIdentity) ++ reprStr (table.disk?.map (fun d => (toJson d.header).compress ++ (toJson d.membership?).compress))) && record.query == query && record.entry == entry then
        let beforeReplay := (← table.budget?.mapM (·.get)).getD {}
        if let some proof := record.proof? then
          let arguments ← xs.filterM fun x => return !(← x.fvarId!.isLetVar)
          goal.assign (proof.beta arguments)
          discard <| checkLookupGoal table (← getEnv) goal
        if let some budget := table.budget? then
          budget.set {beforeReplay with
            coverage := beforeReplay.coverage + record.search + record.preparation,
            preparation := beforeReplay.preparation + record.preparation,
            preparationStart := beforeReplay.preparation + record.preparation}
        lookupPhase s!"lookup/resumed ordinal={ordinal} candidate={entry.name}"
        IO.setNumHeartbeats (startedReplay + record.search)
        return record.trace
      else
        lookupPhase s!"lookup/checkpoint-miss ordinal={ordinal} reason=input-mismatch"
  if resume?.isSome && !candidateOwnerMatches table entry then
    if (← lookupExternalAttempts.get) >= 64 then
      emitLookupRecord s!"LOOKUP_CHECKPOINT_RESTART next={ordinal} candidate={entry.name}"
      IO.Process.exit 75
    lookupExternalAttempts.modify (· + 1)
  IO.setNumHeartbeats startedReplay
  let original ← saveState
  resetCache
  modifyThe Core.State fun state => {state with cache := {}}
  let before := (← table.budget?.mapM (·.get)).getD {}
  if let some budget := table.budget? then
    budget.modify fun state => {state with preparationStart := state.preparation}
  let started ← IO.getNumHeartbeats
  let checkedProof ← IO.mkRef (none : Option Expr)
  let result ← catchLookupCandidate
    (withTheReader Core.Context (fun ctx => {ctx with
      initHeartbeats := started, maxHeartbeats := lookupCandidateBudget * 1000}) do
      let result ← action
      if result.source?.isSome && !table.speculative then
        checkedProof.set (some (← checkLookupGoal table original.core.env goal))
      checkSystem "lookup.candidate"
      return result)
    (fun ex => do
      let after := (← table.budget?.mapM (·.get)).getD {}
      let reason ← if ex.isMaxHeartbeat then pure <|
          if after.preparation - before.preparation >= lookupPreparationBudget * 1000 then
            "preparation-capped" else "capped"
        else if ex.isInterrupt then pure "interrupted"
        else pure s!"exception:{← ex.toMessageData.toString}"
      return {
        complete := false, missing := #[entry.leanName], failures := #[reason],
        capped := if ex.isMaxHeartbeat then #[entry.name] else #[]})
  let search := (← IO.getNumHeartbeats) - started
  let after := (← table.budget?.mapM (·.get)).getD {}
  let preparation := after.preparation - before.preparation
  if let some budget := table.budget? then
    budget.modify fun state => {state with
      coverage := state.coverage + search + preparation, preparationStart := state.preparation,
      candidateSearch := search, candidatePreparation := preparation}
  let residual := Json.mkObj [
    ("module", toJson entry.module), ("candidate", toJson entry.name),
    ("search_internal_heartbeats", toJson search),
    ("preparation_internal_heartbeats", toJson preparation),
    ("capped", toJson (!result.capped.isEmpty)), ("reasons", toJson result.failures)]
  if !result.complete || (← IO.getEnv "SEARCH_REDUCTION_TELEMETRY").isSome then
    emitLookupRecord s!"LOOKUP_CANDIDATE {residual.compress}"
  if result.source?.isNone then
    original.restore
    set original.meta
    modifyThe Core.State fun state => {state with cache := original.core.cache}
  let result := {result with
    visited := 1,
    failures := if result.complete then result.failures else
      result.failures.map (fun reason => s!"{entry.module}:{entry.name}:{reason}")}
  if let some path := checkpoint? then
    if query.hasMVar then throwError "lookup.checkpoint_open_query:{ordinal}"
    IO.FS.createDirAll path.parent.get!
    let temporary := path.addExtension "tmp"
    let identity := (← checkpointIdentity) ++ reprStr (table.disk?.map (fun d => (toJson d.header).compress ++ (toJson d.membership?).compress))
    let proof? ← if result.source?.isSome then checkedProof.get else pure none
    pickle temporary ({
      identity, query, entry, trace := result, proof?, search, preparation} : LookupCheckpoint)
    IO.FS.rename temporary path
  return result

/-- Hashes only recall candidates; equality and a final certificate decide. -/
unsafe def lookupExact (table : LookupTable) (goal : MVarId) : MetaM LookupTrace := goal.withContext do
  if !table.enabled then return {complete := true}
  let some index ← tableIndex table | return {}
  let type ← goal.getType
  let candidates ← DiskLookup.queryMembership index type table.budget?
  let mut trace : LookupTrace := {
    complete := candidates.complete && table.complete,
    pages := candidates.pages, failures := candidates.missing}
  for entry in candidates.entries do
    unless ← coverageAvailable table do
      return {trace with complete := false, failures := trace.failures.push "G-truncated:membership"}
    let attempt ← boundedLookupCandidate table entry goal do
      let candidate ← candidateValue table entry none type
      if let some reason := candidate.failure? then
        return {complete := false, failures := #[reason], missing := #[entry.leanName]}
      for value in candidate.values do
        if ← withReducible <| isDefEq (← inferType value) type then
          candidate.certify
          goal.assign (← instantiateMVars value)
          return {
            complete := true, source? := some entry.leanName, attempted := 1,
            unloaded := if candidate.unloaded then 1 else 0}
      return {complete := true, unloaded := if candidate.unloaded then 1 else 0}
    trace := mergeLookupTrace trace attempt
    if trace.source?.isSome then return trace
  return trace

/-- A member certificate must be recalled by the full-B0 alpha hash. Naming
an arbitrary definitionally equal declaration does not bypass membership. -/
unsafe def lookupNamedMember (table : LookupTable) (name : Name)
    (goal : MVarId) : MetaM LookupTrace := goal.withContext do
  if !table.enabled then return {}
  let some index ← tableIndex table | return {}
  let type ← goal.getType
  let candidates ← DiskLookup.queryMembership index type table.budget?
  let some entry := candidates.entries.find? (·.leanName == name) | return {}
  boundedLookupCandidate table entry goal do
    let candidate ← candidateValue table entry none type
    if let some reason := candidate.failure? then
      return {failures := #[reason], missing := #[name]}
    for value in candidate.values do
      if ← withReducible <| isDefEq (← inferType value) type then
        candidate.certify
        goal.assign (← instantiateMVars value)
        return {complete := true, source? := some name, attempted := 1}
    return {complete := true}

/-- Hash recall is a nominator, not a negative certificate. -/
unsafe def memberCertificateNames (table : LookupTable) (type : Expr) : MetaM (Array Name) := do
  if !table.enabled then return #[]
  let some index ← tableIndex table | return #[]
  let candidates ← DiskLookup.queryMembership index type table.budget?
  return candidates.entries.map (·.leanName)

partial def inlineLookupSupport (base : Environment) (proof : Expr)
    (seen : NameSet := {}) : MetaM Expr :=
  Core.transform proof (pre := fun e => do
    if let .const name levels := e then
      unless (base.setExporting false).contains name do
        if seen.contains name then throwError "lookup.recursive-support:{name}"
        let info ← getConstInfo name
        if info.isUnsafe then throwError "lookup.unsafe_support:{name}"
        let some body := info.value? (allowOpaque := true)
          | throwError "lookup.support_requires_import:{name}"
        let body ← inlineLookupSupport base
          (body.instantiateLevelParams info.levelParams levels) (seen.insert name)
        return .done body
    return .continue)

/-- A wildcard denotes a head which reduction or instantiation may change.
Only rigid unequal heads can be discarded without testing an application. -/
private partial def rigidHead (env : Environment) (e : Expr) (fuel : Nat := 32) : Option Name :=
  if fuel == 0 then none else
  match e.consumeMData with
  | .forallE _ _ body _ => rigidHead env body (fuel - 1)
  | .letE _ _ value body _ => rigidHead env (body.instantiate1 value) (fuel - 1)
  | e => match e.getAppFn with
    | .const n levels =>
      match env.find? n with
      | some (.defnInfo value) =>
        if getReducibilityStatusCore env n == .reducible then
          rigidHead env ((value.value.instantiateLevelParams value.levelParams levels).beta e.getAppArgs)
            (fuel - 1)
        else if (env.getProjectionFnInfo? n).isSome then none else some n
      | some (.recInfo _) => none
      | _ => some n
    | _ => none

private partial def possibleView (env : Environment) (head : Option Name)
    (type : Expr) : Bool :=
  let body := type.consumeMData
  match body with
  | .forallE _ _ rest _ => possibleView env head rest
  | .letE _ _ value rest _ => possibleView env head (rest.instantiate1 value)
  | _ =>
    if body.isAppOfArity ``And 2 || body.isAppOfArity ``Iff 2 then
      possibleView env head (body.getArg! 0) || possibleView env head (body.getArg! 1) ||
        rigidHead env body == head
    else if body.isAppOfArity ``Subtype 2 then true
    else if body.isAppOfArity ``Eq 3 && body.getArg! 0 == mkSort .zero then true
    else if body.getAppFn.constName?.any (fun n =>
        getReducibilityStatusCore env n == .reducible) then true
    else match rigidHead env body, head with
      | some a, some b => a == b
      | _, _ => true

/-- A detached module has no extension state. All definition and recursor
heads therefore stay wildcard; only intrinsically rigid unequal heads reject. -/
partial def unloadedPossibleView (env : Environment) (head : Option Name) (type : Expr) : Bool :=
  match type.consumeMData with
  | .forallE _ _ body _ => unloadedPossibleView env head body
  | .letE _ _ value body _ => unloadedPossibleView env head (body.instantiate1 value)
  | body =>
    if body.isAppOfArity ``And 2 || body.isAppOfArity ``Iff 2 then
      unloadedPossibleView env head (body.getArg! 0) ||
        unloadedPossibleView env head (body.getArg! 1) || head == body.getAppFn.constName?
    else if body.isAppOfArity ``Subtype 2 then true
    else if body.isAppOfArity ``Eq 3 && body.getArg! 0 == mkSort .zero then true
    else match body.getAppFn.constName?, head with
      | some name, some target =>
        match (env.setExporting false).find? name with
        | some (.inductInfo _) | some (.ctorInfo _) | some (.axiomInfo _) |
            some (.opaqueInfo _) | some (.thmInfo _) => name == target
        | _ => true
      | _, _ => true

partial def unloadedDirectView (env : Environment) (head : Option Name) (type : Expr) : Bool :=
  match type.consumeMData with
  | .forallE _ _ body _ => unloadedDirectView env head body
  | .letE _ _ value body _ => unloadedDirectView env head (body.instantiate1 value)
  | body =>
    match body.getAppFn.constName?, head with
    | some name, some target =>
      match (env.setExporting false).find? name with
      | some (.inductInfo _) | some (.ctorInfo _) | some (.axiomInfo _) |
          some (.opaqueInfo _) | some (.thmInfo _) => name == target
      | _ => true
    | _, _ => true

/-- Projection is performed inside the source telescope. Its data parameters
are subsequently determined by application unification, never enumeration. -/
partial def views (value : Expr) : MetaM (Array Expr) := do
  checkSystem "lookup.views"
  forallTelescopeReducing (← inferType value) fun xs body => do
    let applied := mkAppN value xs
    let body ← withReducible <| whnf body
    let mut result := #[value]
    if body.isAppOfArity ``And 2 then
      for projection in #[``And.left, ``And.right] do
        let projected ← mkAppM projection #[applied]
        let projected ← mkLambdaFVars xs projected
        result := result ++ (← views projected)
    if body.isAppOfArity ``Iff 2 then
      for direction in #[``Iff.mp, ``Iff.mpr] do
        result := result.push (← mkLambdaFVars xs (← mkAppM direction #[applied]))
    if body.isAppOfArity ``Eq 3 then
      result := result.push (← mkLambdaFVars xs (← mkAppM ``Eq.symm #[applied]))
      if body.getArg! 0 == mkSort .zero then
        for direction in #[``Eq.mp, ``Eq.mpr] do
          result := result.push (← mkLambdaFVars xs (← mkAppM direction #[applied]))
    if body.isAppOfArity ``Subtype 2 then
      let projected ← mkLambdaFVars xs (← mkAppM ``Subtype.property #[applied])
      result := result ++ (← views projected)
    return result

/-- A fresh metavariable stands only for the candidate signature. No proof
body is read until application and the frozen closure table both succeed. The
placeholder never leaves the branch: success materializes it before checking. -/
@[noinline] def copyLookupCandidateWith (copy : Environment → Expr → MetaM Expr)
    (source : Environment) (entry : DiskLookup.Entry) (head : Option Name)
    (budget? : Option (IO.Ref LookupBudgetState) := none) : MetaM LookupCandidate := do
  let some info := (source.setExporting false).find? entry.leanName
    | throwError "lookup.module_candidate_missing"
  if info.isUnsafe then return {}
  unless unloadedPossibleView source head info.type do return {}
  match info with
  | .thmInfo _ | .defnInfo _ | .opaqueInfo _ => pure ()
  | _ => return {}
  let params := info.levelParams.map ownedLookupName
  let levels ← params.mapM fun _ => mkFreshLevelMVar
  let signature ← withLookupPreparation budget? <| pure <|
    detachLookupExpression (info.type.instantiateLevelParams info.levelParams levels)
  let type ← timeLookup "candidate/signature" <| copy source signature
  let type ← withLookupPreparation budget? <| pure (detachLookupExpression type)
  let placeholder ← mkFreshExprMVar type
  return {values := #[placeholder], certify := do
    lookupPhase s!"candidate/signature-matched name={entry.name} module={entry.module}"
    let some body := info.value? (allowOpaque := true)
      | throwError "lookup.candidate_value_missing"
    let body ← withLookupPreparation budget? <| pure <|
      detachLookupExpression (body.instantiateLevelParams info.levelParams levels)
    let proof ← timeLookup "candidate/transport" <| copy source body
    let proof ← withLookupPreparation budget? <| pure (detachLookupExpression proof)
    placeholder.mvarId!.assign proof}

/-- Shared candidate attempt used by enumeration and focused regressions. -/
unsafe def attemptLookupLeaf (table : LookupTable) (entry : DiskLookup.Entry)
    (goal : MVarId) (unify close : MVarId → MetaM Bool) : MetaM LookupTrace := goal.withContext do
  let head := rigidHead (← getEnv) (← goal.getType)
  boundedLookupCandidate table entry goal do
    let name := entry.leanName
    if let some info := (table.environment.setExporting false).find? name |>.filter (fun _ => candidateOwnerMatches table entry) then
      if !eligible info || info.isUnsafe || !possibleView table.environment head info.type then
        return {complete := true}
    let candidate ← candidateValue table entry head (← goal.getType)
    if let some reason := candidate.failure? then
      return {
        complete := false, failures := #[reason], missing := #[name],
        unloaded := if candidate.unloaded then 1 else 0}
    let mut attempted := 0
    for value in candidate.values do
      let type ← inferType value
      unless possibleView (← getEnv) head type do continue
      let suitable ← if ← isProp type then pure true else
        forallTelescopeReducing type fun _ body => do
          return (← withReducible <| whnf body).isAppOfArity ``Subtype 2
      unless suitable do continue
      let alternatives ← views value
      for view in alternatives do
        let saved ← saveState
        attempted := attempted + 1
        -- Ordinary apply failure tries the next view. Resource failure and
        -- unsupported views escape to the candidate-local boundary.
        let matched ← try
          let obligations ← withReducible <| goal.apply view {approx := false}
          let obligations := obligations.filter fun next =>
            !candidate.values.any (fun value => value.isMVar && value.mvarId! == next)
          let propositions ← obligations.filterM fun g => g.withContext do isProp (← g.getType)
          for next in propositions do
            if (← instantiateMVars (← next.getType)).hasMVar then discard <| unify next
          let dataClosed ← obligations.allM fun next => do
            if ← next.isAssigned then return true
            next.withContext do isProp (← instantiateMVars (← next.getType))
          pure (dataClosed && (← propositions.allM fun next => do
            if ← next.isAssigned then return true else close next))
        catch ex =>
          if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
          pure false
        if matched then
          candidate.certify
          let proof ← instantiateMVars (mkMVar goal)
          unless proof.hasMVar do return {
            complete := true, source? := some name, attempted,
            unloaded := if candidate.unloaded then 1 else 0}
        saved.restore
    return {complete := true, attempted, unloaded := if candidate.unloaded then 1 else 0}

/-- Exactly the production primary-index recall and v16 single-candidate
attempt. In particular, naming a star or out-of-B_T theorem cannot admit it. -/
unsafe def lookupNamedLeaf (table : LookupTable) (name : Name) (goal : MVarId)
    (unify close : MVarId → MetaM Bool) : MetaM LookupTrace := goal.withContext do
  if !table.enabled then return {}
  let some index ← tableIndex table | return {}
  let candidates ← queryLookup table index (← goal.getType) none false
  let some entry := candidates.entries.find? (·.leanName == name) | return {}
  attemptLookupLeaf table entry goal unify close

/-- Only loaded candidates may run concurrently: importing and freeing a
temporary module remains owned by the serial thread. Each task receives the
same persistent Core/Meta snapshot and a separate preparation/coverage ref.
Task results are consumed in the original candidate order. A possible success
is replayed serially, including transport and the final kernel certificate. -/
private unsafe def speculateLookupCandidates (table : LookupTable)
    (entries : Array DiskLookup.Entry) (goal : MVarId)
    (unify close : MVarId → MetaM Bool) :
    MetaM (Array (LookupTrace × LookupBudgetState)) := do
  let metaContext ← readThe Meta.Context
  let metaState ← getThe Meta.State
  let coreContext ← readThe Core.Context
  let coreState ← getThe Core.State
  let mut tasks := #[]
  for entry in entries do
    -- Environment realization caches are shared. Reserve disjoint names just
    -- as Core.wrapAsync does, even though each task discards its own state.
    let (ngen, parentNGen) := (← getNGen).mkChild
    setNGen parentNGen
    let (auxDeclNGen, parentDeclNGen) := (← getDeclNGen).mkChild
    setDeclNGen parentDeclNGen
    let state := {coreState with ngen, auxDeclNGen}
    let action : MetaM (LookupTrace × LookupBudgetState) := do
      let budget ← IO.mkRef ({} : LookupBudgetState)
      let trace ← attemptLookupLeaf
        {table with budget? := some budget, speculative := true} entry goal unify close
      return (trace, ← budget.get)
    let work := Core.withCurrHeartbeats (action.run' metaContext metaState)
    tasks := tasks.push (← EIO.asTask (work.run' coreContext state))
  -- Join all tasks before releasing the shared snapshot or module storage.
  let results := tasks.map (·.get)
  results.mapM MonadExcept.ofExcept

/-- The frozen closure table has lookup disabled. Every candidate exception
is accounted for locally; only the coverage guard truncates enumeration. -/
unsafe def lookupLeafPass (table : LookupTable) (goal : MVarId)
    (unify close : MVarId → MetaM Bool) : MetaM LookupTrace := goal.withContext do
  if !table.enabled then return {complete := true}
  let some index ← tableIndex table | return {}
  let telemetry := (← IO.getEnv "SEARCH_REDUCTION_TELEMETRY").isSome
  let floorStart ← IO.getNumHeartbeats
  let floorNs ← IO.monoNanosNow
  let beforePreparation := (← table.budget?.mapM (·.get)).getD {}
  -- Revision 16 uses only the primary implication-index route. The star
  -- fallback remains available as historical/static-pruning evidence, but is
  -- deliberately excluded from production enumeration and NoHit accounting.
  let candidates ← queryLookup table index (← goal.getType) none false
  if telemetry then
    let afterPreparation := (← table.budget?.mapM (·.get)).getD {}
    emitLookupRecord s!"LOOKUP_TELEMETRY_FLOOR {Json.mkObj [
      ("fallback_only", toJson false), ("entries", toJson candidates.entries.size),
      ("search_internal_heartbeats", toJson ((← IO.getNumHeartbeats) - floorStart)),
      ("preparation_internal_heartbeats", toJson (afterPreparation.preparation - beforePreparation.preparation)),
      ("ns", toJson ((← IO.monoNanosNow) - floorNs))] |>.compress}"
  let workers := min 8 <| max 1 <|
    ((← IO.getEnv "SEARCH_REDUCTION_WORKERS").bind String.toNat?).getD 8
  let mut ordinal := 0
  let mut trace : LookupTrace := {
    complete := candidates.complete && table.complete,
    pages := candidates.pages}
  let mut pending : Array (LookupTrace × LookupBudgetState) := #[]
  let mut pendingStart := 0
  for entry in candidates.entries do
    let position := ordinal
    ordinal := ordinal + 1
    unless ← coverageAvailable table do
      trace := {trace with
        complete := false, failures := trace.failures.push s!"G-truncated:primary-index:remaining={candidates.entries.size - trace.visited}"}
      break
    if position % 128 == 0 then
      emitLookupRecord s!"LOOKUP_ENUMERATION_PROGRESS fallback=false next={position} total={candidates.entries.size}"
    if workers > 1 &&
        (position < pendingStart || position >= pendingStart + pending.size) then
      let mut batch := #[]
      let queue := workers
      for next in candidates.entries[position:min candidates.entries.size (position + queue)] do
        unless candidateOwnerMatches table next do break
        batch := batch.push next
      pendingStart := position
      pending ← if batch.size > 1 then
        speculateLookupCandidates table batch goal unify close else pure #[]
    let result ← if let some (speculated, usage) := pending[position - pendingStart]? then do
        if speculated.source?.isSome then
          -- No speculative proof or state is admitted as a certificate.
          attemptLookupLeaf table entry goal unify close
        else do
          lookupAttemptOrdinal.modify (· + 1)
          IO.addHeartbeats usage.candidateSearch
          if let some budget := table.budget? then
            budget.modify fun state => {state with
              preparation := state.preparation + usage.preparation,
              preparationNs := state.preparationNs + usage.preparationNs,
              preparationStart := state.preparation + usage.preparation,
              coverage := state.coverage + usage.coverage}
          pure speculated
      else attemptLookupLeaf table entry goal unify close
    trace := mergeLookupTrace trace result
    if trace.source?.isSome then break
  unless telemetry do emitLookupRecord s!"LOOKUP_ENUMERATION {Json.mkObj [
    ("fallback", toJson false), ("total", toJson candidates.entries.size),
    ("static_normal_failures", toJson candidates.staticFailures),
    ("visited", toJson trace.visited), ("complete", toJson trace.complete),
    ("found", toJson trace.source?.isSome), ("capped", toJson trace.capped),
    ("unknown", toJson trace.failures)] |>.compress}"
  return trace

unsafe def lookupLeaf (table : LookupTable) (goal : MVarId)
    (unify close : MVarId → MetaM Bool) : MetaM LookupTrace := do
  lookupLeafPass table goal unify close

end LeanInformationAudit.SearchReduction
