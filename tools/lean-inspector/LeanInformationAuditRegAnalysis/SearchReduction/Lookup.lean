import LeanInformationAuditRegAnalysis.SearchReduction.DiskLookup

/-! One-basis-declaration retrieval from checked disk pages. No query scans
the baseline environment or constructs an environment-wide tree. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta

def lookupPhase (label : String) : IO Unit := do
  if let some path ← IO.getEnv "SEARCH_REDUCTION_PROFILE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn s!"{← IO.monoMsNow} {label}"

abbrev lookupVersion : String := "R_lookup/one-B/discrtree-pickle-v2-independent"

/-- The table is captured before delivery vocabulary or S is installed. A
partial basis may supply a hit, but never a completed negative query. -/
structure LookupTable where
  environment : Environment
  complete : Bool := true
  enabled : Bool := true
  disk? : Option DiskLookup.Index := none
  load? : Option (DiskLookup.Entry → Option Name → MetaM (Array Expr × Array String)) := none
  close? : Option (IO Unit) := none
  finish? : Option (Environment → Expr → MetaM Expr) := none

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

private def candidateValue (table : LookupTable) (entry : DiskLookup.Entry) (head : Option Name) :
    MetaM (Array Expr × Option String × Bool) := do
  if let some info := (table.environment.setExporting false).find? entry.leanName then
    if !eligible info || info.isUnsafe then return (#[], none, false)
    return (#[← mkConstWithFreshMVarLevels entry.leanName], none, false)
  let some load := table.load? | return (#[], some "candidate-not-loaded", true)
  try
    let (values, failures) ← load entry head
    return (values, if failures.isEmpty then none else some s!"{failures}", true)
  catch ex =>
    if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
    return (#[], some s!"candidate-certification:{← ex.toMessageData.toString}", true)

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
  return {table with disk?, complete := table.complete && disk?.any (·.header.complete)}

/-- The membership page is only a prefilter. Alpha-invariant hashes never
substitute for definitional equality or the caller's closed kernel check. -/
private unsafe def lookupExactPass (fallback : Bool) (table : LookupTable) (goal : MVarId) : MetaM LookupTrace := goal.withContext do
  if !table.enabled then return {complete := true}
  let some index ← tableIndex table | return {}
  let type ← goal.getType
  let context ← readThe Core.Context
  let limit := if context.maxHeartbeats == 0 then none
    else some (context.initHeartbeats + context.maxHeartbeats)
  let candidates ← DiskLookup.queryMature index type limit fallback
  checkSystem "lookup.membership-index"
  let mut trace : LookupTrace := {complete := candidates.complete && table.complete, pages := candidates.pages}
  for entry in candidates.entries do
    checkSystem "lookup.membership"
    let name := entry.leanName
    let saved ← saveState
    let (values, failure?, unloaded) ← candidateValue table entry none
    trace := {trace with unloaded := trace.unloaded + (if unloaded then 1 else 0)}
    if let some failure := failure? then
      trace := {trace with
        complete := false
        missing := trace.missing.push name
        failures := trace.failures.push s!"{name}:{failure}"}
    trace := {trace with visited := trace.visited + 1}
    for value in values do
      if ← withReducible <| isDefEq (← inferType value) type then
        goal.assign value
        return {trace with source? := some name, attempted := trace.attempted + 1}
    saved.restore
    set saved.meta
    modifyThe Core.State fun state => {state with cache := saved.core.cache}
  return trace

unsafe def lookupExact (table : LookupTable) (goal : MVarId) : MetaM LookupTrace := do
  let primary ← lookupExactPass false table goal
  if primary.source?.isSome then return primary
  let fallback ← lookupExactPass true table goal
  return {fallback with
    complete := primary.complete && fallback.complete,
    visited := primary.visited + fallback.visited, pages := primary.pages + fallback.pages,
    attempted := primary.attempted + fallback.attempted,
    missing := primary.missing ++ fallback.missing, failures := primary.failures ++ fallback.failures}

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
  let candidates ← DiskLookup.queryMature index (← goal.getType) limit fallback
  checkSystem "lookup.candidate-index"
  let trace ← candidates.entries.foldlM (init := ({complete := candidates.complete && table.complete, pages := candidates.pages} : LookupTrace)) fun (trace : LookupTrace) entry => do
    if trace.source?.isSome then return trace
    checkSystem "lookup.page_candidate"
    let name := entry.leanName
    if let some info := (table.environment.setExporting false).find? name then
      if !eligible info || info.isUnsafe || !possibleView table.environment head info.type then
        return {trace with visited := trace.visited + 1}
    let initial ← get
    let cache := (← getThe Core.State).cache
    let original ← saveState
    let (values, failure?, unloaded) ← candidateValue table entry head
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
    let alternatives : Array Expr ← if unloaded then pure values else (do
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
        let obligations ← withReducible <| goal.apply view {approx := false}
        let propositions ← obligations.filterM fun g => g.withContext do isProp (← g.getType)
        -- Only visible-fact unification may recover parameters absent from
        -- the conclusion. Decision procedures cannot invent a data argument.
        for next in propositions do
          if (← instantiateMVars (← next.getType)).hasMVar then discard <| unify next
        let dataClosed ← obligations.allM fun next => do
          if ← next.isAssigned then return true
          next.withContext do isProp (← instantiateMVars (← next.getType))
        if dataClosed && (← propositions.allM fun next => do
            if ← next.isAssigned then return true else close next) then
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
