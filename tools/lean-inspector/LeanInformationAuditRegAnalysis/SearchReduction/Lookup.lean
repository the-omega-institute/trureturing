import LeanInformationAuditRegAnalysis.SearchReduction.DiskLookup

/-! One-basis-declaration retrieval from checked disk pages. No query scans
the baseline environment or constructs an environment-wide tree. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta

def lookupPhase (label : String) : IO Unit := do
  if let some path ← IO.getEnv "SEARCH_REDUCTION_PROFILE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn s!"{← IO.monoMsNow} {label}"

/-- Includes exceptional exits; nested spans must not be added to their parent. -/
def timeLookup {α : Type} (label : String) (action : MetaM α) : MetaM α := do
  if (← IO.getEnv "SEARCH_REDUCTION_PROFILE").isNone then return ← action
  let start ← IO.monoNanosNow
  let heartbeats ← IO.getNumHeartbeats
  lookupPhase s!"{label}/start"
  try action finally
    lookupPhase s!"{label}/end ns={(← IO.monoNanosNow) - start} heartbeats={(← IO.getNumHeartbeats) - heartbeats}"

abbrev lookupVersion : String := "R_lookup/v6/signature-first/search-200000/preparation-2000000/N-memo-2000000"

/-- Bounded, query-local metadata reuse; certificates are always checked anew. -/
structure LookupQueryMemo where
  primary? : Option (Environment × Expr × DiskLookup.Candidates) := none
  fallback? : Option DiskLookup.Candidates := none
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
  complete : Bool := true
  enabled : Bool := true
  disk? : Option DiskLookup.Index := none
  load? : Option (DiskLookup.Entry → Option Name → MetaM LookupCandidate) := none
  close? : Option (IO Unit) := none
  finish? : Option (Environment → Expr → MetaM Expr) := none
  memo? : Option (IO.Ref LookupQueryMemo) := none
  budget? : Option (IO.Ref LookupBudgetState) := none

structure LookupTrace where
  visited : Nat := 0
  attempted : Nat := 0
  pages : Nat := 0
  missing : Array Name := #[]
  failures : Array String := #[]
  unloaded : Nat := 0
  source? : Option Name := none
  complete : Bool := false
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

private def candidateValue (table : LookupTable) (entry : DiskLookup.Entry) (head : Option Name) :
    MetaM LookupCandidate := do
  if let some info := (table.environment.setExporting false).find? entry.leanName |>.filter (fun _ => candidateOwnerMatches table entry) then
    if !eligible info || info.isUnsafe then return {}
    return {values := #[← mkConstWithFreshMVarLevels entry.leanName]}
  let some load := table.load? | return {failure? := some "candidate-not-loaded", unloaded := true}
  try
    let result ← load entry head
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
  -- Recompute matching in every reset search branch; only module bytes cache.
  let candidates ← DiskLookup.queryMature index type limit fallback table.budget?
  withLookupPreparation table.budget? do
    let (loaded, external) := candidates.entries.partition (candidateOwnerMatches table)
    return {candidates with entries := loaded ++ external}

/-- The membership page is only a prefilter. Alpha-invariant hashes never
substitute for definitional equality or the caller's closed kernel check. -/
private unsafe def lookupExactPass (table : LookupTable) (goal : MVarId) : MetaM LookupTrace := goal.withContext do
  if !table.enabled then return {complete := true}
  let some index ← tableIndex table | return {}
  let type ← goal.getType
  let indexStart ← IO.monoMsNow
  let candidates ← DiskLookup.queryMembership index type table.budget?
  let candidates ← withLookupPreparation table.budget? do
    let (loaded, external) := candidates.entries.partition (candidateOwnerMatches table)
    return {candidates with entries := loaded ++ external}
  lookupPhase s!"lookup/index ms={(← IO.monoMsNow) - indexStart} membership=true"
  profileCandidateSet table type candidates false "exact"
  checkSystem "lookup.membership-index"
  let mut trace : LookupTrace := {
    complete := candidates.complete && table.complete
    pages := candidates.pages
    failures := candidates.missing}
  for entry in candidates.entries do
    checkSystem "lookup.membership"
    let name := entry.leanName
    let saved ← saveState
    lookupPhase s!"lookup/visit mode=exact name={name} module={entry.module}"
    let candidate ← timeLookup "lookup/load" <| candidateValue table entry none
    let values := candidate.values
    let failure? := candidate.failure?
    let unloaded := candidate.unloaded
    trace := {trace with unloaded := trace.unloaded + (if unloaded then 1 else 0)}
    if let some failure := failure? then
      trace := {trace with
        complete := false
        missing := trace.missing.push name
        failures := trace.failures.push s!"{name}:{failure}"}
    trace := {trace with visited := trace.visited + 1}
    for value in values do
      if ← timeLookup "lookup/isDefEq" (withReducible <| isDefEq (← inferType value) type) then
        timeLookup "candidate/certificate" candidate.certify
        goal.assign (← instantiateMVars value)
        return {trace with source? := some name, attempted := trace.attempted + 1}
    saved.restore
    set saved.meta
    modifyThe Core.State fun state => {state with cache := saved.core.cache}
  return trace

unsafe def lookupExact (table : LookupTable) (goal : MVarId) : MetaM LookupTrace := do
  lookupExactPass table goal

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

/-- The result must own every byte before its temporary module regions close. -/
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
partial def views (value : Expr) (fuel : Nat := 32) : MetaM (Array Expr) := do
  if fuel == 0 then throwError "lookup.view_depth_incomplete"
  forallTelescopeReducing (← inferType value) fun xs body => do
    let applied := mkAppN value xs
    let body ← withReducible <| whnf body
    let mut result := #[value]
    if body.isAppOfArity ``And 2 then
      for projection in #[``And.left, ``And.right] do
        let projected ← mkAppM projection #[applied]
        let projected ← mkLambdaFVars xs projected
        result := result ++ (← views projected (fuel - 1))
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
      result := result ++ (← views projected (fuel - 1))
    return result

/-- A fresh metavariable stands only for the candidate signature. No proof
body is read until application and the frozen closure table both succeed. The
placeholder never leaves the branch: success materializes it before checking. -/
@[noinline] def copyLookupCandidateWith (copy : Environment → Expr → MetaM Expr)
    (source : Environment) (entry : DiskLookup.Entry) (head : Option Name) :
    MetaM LookupCandidate := do
  let some info := (source.setExporting false).find? entry.leanName
    | throwError "lookup.module_candidate_missing"
  if info.isUnsafe then return {}
  unless unloadedPossibleView source head info.type do return {}
  match info with
  | .thmInfo _ | .defnInfo _ | .opaqueInfo _ => pure ()
  | _ => return {}
  let params := info.levelParams.map ownedLookupName
  let levels ← params.mapM fun _ => mkFreshLevelMVar
  let type ← timeLookup "candidate/signature" <| copy source
    (info.type.instantiateLevelParams info.levelParams levels)
  let type := detachLookupExpression type
  let placeholder ← mkFreshExprMVar type
  return {values := #[placeholder], certify := do
    lookupPhase s!"candidate/signature-matched name={entry.name} module={entry.module}"
    let some body := info.value? (allowOpaque := true)
      | throwError "lookup.candidate_value_missing"
    let proof ← timeLookup "candidate/transport" <| copy source
      (body.instantiateLevelParams info.levelParams levels)
    let proof ← withLookupPreparation none <| pure (detachLookupExpression proof)
    placeholder.mvarId!.assign proof}

/-- The closure callback is the frozen local table, with lookup disabled.
All unresolved data and universe metavariables are rejected by the caller's
closed kernel certificate check. An exception aborts enumeration. -/
private unsafe def lookupLeafPass (fallback : Bool) (table : LookupTable) (goal : MVarId)
    (unify close : MVarId → MetaM Bool) : MetaM LookupTrace := goal.withContext do
  if !table.enabled then return {complete := true}
  let detailed := (← IO.getEnv "SEARCH_REDUCTION_PROFILE_DETAIL").isSome
  let head := rigidHead (← getEnv) (← goal.getType)
  let some index ← tableIndex table | return {}
  let context ← readThe Core.Context
  let limit := if context.maxHeartbeats == 0 then none
    else some (context.initHeartbeats + context.maxHeartbeats)
  let indexStart ← IO.monoMsNow
  let candidates ← queryLookup table index (← goal.getType) limit fallback
  lookupPhase s!"lookup/index ms={(← IO.monoMsNow) - indexStart} fallback={fallback}"
  profileCandidateSet table (← goal.getType) candidates fallback "leaf"
  checkSystem "lookup.candidate-index"
  let trace ← candidates.entries.foldlM (init := ({complete := candidates.complete && table.complete, pages := candidates.pages} : LookupTrace)) fun (trace : LookupTrace) entry => do
    if trace.source?.isSome then return trace
    checkSystem "lookup.page_candidate"
    let name := entry.leanName
    if let some info := (table.environment.setExporting false).find? name |>.filter (fun _ => candidateOwnerMatches table entry) then
      if !eligible info || info.isUnsafe || !possibleView table.environment head info.type then
        return {trace with visited := trace.visited + 1}
    let initial ← get
    let cache := (← getThe Core.State).cache
    let original ← saveState
    lookupPhase s!"lookup/visit mode=leaf name={name} module={entry.module}"
    let candidate ← timeLookup "lookup/load" <| candidateValue table entry head
    let values := candidate.values
    let failure? := candidate.failure?
    let unloaded := candidate.unloaded
    let trace := {trace with unloaded := trace.unloaded + (if unloaded then 1 else 0)}
    let trace := if let some failure := failure? then
        {trace with
          complete := false
          missing := trace.missing.push name
          failures := trace.failures.push s!"{name}:{failure}"}
      else trace
    if values.isEmpty then
      original.restore
      set initial
      modifyThe Core.State fun state => {state with cache}
      return trace
    let trace := {trace with visited := trace.visited + 1}
    let alternatives : Array Expr ← (do
      let value := values[0]!
      let type ← inferType value
      unless possibleView (← getEnv) head type do return #[]
      let suitable : Bool ← (do
        if ← isProp type then return true
        forallTelescopeReducing type fun _ body => do
          return (← withReducible <| whnf body).isAppOfArity ``Subtype 2 : MetaM Bool)
      if suitable then views value else pure #[] : MetaM (Array Expr))
    let mut attempted := trace.attempted
    for view in alternatives do
      let saved ← saveState
      attempted := attempted + 1
      if detailed then
        lookupPhase s!"lookup/candidate-start name={name} visited={trace.visited} attempted={attempted}"
      try
        let obligations ← timeLookup "lookup/apply" <| withReducible <| goal.apply view {approx := false}
        let (propositions, dataClosed) ← timeLookup "lookup/instantiate" do
          let propositions ← obligations.filterM fun g => g.withContext do isProp (← g.getType)
          -- Only visible facts may recover data absent from the conclusion.
          for next in propositions do
            if (← instantiateMVars (← next.getType)).hasMVar then discard <| unify next
          let dataClosed ← obligations.allM fun next => do
            if ← next.isAssigned then return true
            next.withContext do isProp (← instantiateMVars (← next.getType))
          return (propositions, dataClosed)
        if dataClosed && (← timeLookup "lookup/closure" <| propositions.allM fun next => do
            if ← next.isAssigned then return true else close next) then
          -- Materialize only after the signature and all side conditions match.
          -- Any remaining data metavariable still fails the closed proof check.
          timeLookup "candidate/certificate" candidate.certify
          let proof ← instantiateMVars (mkMVar goal)
          unless proof.hasMVar do return {trace with attempted, source? := some name}
      catch ex =>
        if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
      if detailed then lookupPhase s!"lookup/candidate-end name={name} attempted={attempted}"
      saved.restore
    original.restore
    set initial
    modifyThe Core.State fun s => {s with cache}
    return {trace with attempted}
  return {trace with complete := trace.source?.isNone && trace.complete}

unsafe def lookupLeaf (table : LookupTable) (goal : MVarId)
    (unify close : MVarId → MetaM Bool) : MetaM LookupTrace := do
  let primary ← lookupLeafPass false table goal unify close
  if primary.source?.isSome then return primary
  let fallback ← lookupLeafPass true table goal unify close
  return {fallback with
    complete := primary.complete && fallback.complete,
    visited := primary.visited + fallback.visited, pages := primary.pages + fallback.pages,
    attempted := primary.attempted + fallback.attempted,
    missing := primary.missing ++ fallback.missing, failures := primary.failures ++ fallback.failures}

end LeanInformationAudit.SearchReduction
