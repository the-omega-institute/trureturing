import Lean

/-! One-basis-declaration retrieval. This streaming backend deliberately owns
no environment-wide tree. A paged backend must preserve this query contract. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta

abbrev lookupVersion : String := "R_lookup/one-B/stream-v2-independent"

/-- The table is captured before delivery vocabulary or S is installed. A
partial basis may supply a hit, but never a completed negative query. -/
structure LookupTable where
  environment : Environment
  complete : Bool := true
  enabled : Bool := true

structure LookupTrace where
  visited : Nat := 0
  attempted : Nat := 0
  source? : Option Name := none
  complete : Bool := false
  deriving Inhabited

private def eligible : ConstantInfo → Bool
  | .thmInfo _ | .defnInfo _ | .opaqueInfo _ => true
  | _ => false

/-- The fast membership pass retains no bucket and checks hash collisions by
unification. Expr hashes ignore binder names; no hash is a proof certificate. -/
def lookupExact (table : LookupTable) (goal : MVarId) : MetaM LookupTrace := goal.withContext do
  if !table.enabled then return {complete := true}
  let type ← goal.getType
  table.environment.constants.foldM (init := ({} : LookupTrace)) fun trace name info => do
    if trace.source?.isSome then return trace
    checkSystem "lookup.membership"
    let trace := {trace with visited := trace.visited + 1}
    if !eligible info || info.isUnsafe || info.type.hash != type.hash then return trace
    let saved ← saveState
    let value ← mkConstWithFreshMVarLevels name
    if ← withReducible <| isDefEq (← inferType value) type then
      goal.assign value
      return {trace with source? := some name, attempted := trace.attempted + 1}
    saved.restore
    return trace

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

/-- Projection is performed inside the source telescope. Its data parameters
are subsequently determined by application unification, never enumeration. -/
private partial def views (value : Expr) (fuel : Nat := 32) : MetaM (Array Expr) := do
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
def lookupLeaf (table : LookupTable) (goal : MVarId)
    (unify close : MVarId → MetaM Bool) : MetaM LookupTrace := goal.withContext do
  if !table.enabled then return {complete := true}
  let head := rigidHead (← getEnv) (← goal.getType)
  let trace ← table.environment.constants.foldM (init := ({} : LookupTrace)) fun trace name info => do
    if trace.source?.isSome then return trace
    checkSystem "lookup.scan"
    let trace := {trace with visited := trace.visited + 1}
    if !eligible info || info.isUnsafe then return trace
    unless possibleView table.environment head info.type do return trace
    let initial ← get
    let cache := (← getThe Core.State).cache
    let suitable ← withEnv table.environment do
      if ← isProp info.type then return true
      forallTelescopeReducing info.type fun _ body => do
        return (← withReducible <| whnf body).isAppOfArity ``Subtype 2
    unless suitable do
      set initial
      modifyThe Core.State fun s => {s with cache}
      return trace
    let original ← saveState
    let value ← mkConstWithFreshMVarLevels name
    let alternatives ← views value
    let mut attempted := trace.attempted
    for view in alternatives do
      let saved ← saveState
      attempted := attempted + 1
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
      saved.restore
    original.restore
    set initial
    modifyThe Core.State fun s => {s with cache}
    return {trace with attempted}
  return {trace with complete := trace.source?.isNone && table.complete}

end LeanInformationAudit.SearchReduction
