import Mathlib.Tactic
import LeanInformationAuditRegTests.SearchReduction.Model

/-! Lean-native, Observe-only reference search. Imported candidate extensions
are never copied into either probe environment. Proof terms, not JSON, carry
success; a completed list of unsuccessful attempts carries exhaustion. -/

namespace LeanInformationAudit.SearchReduction
open Lean Meta Elab Tactic Command
open LeanInformationAudit.Tests.SearchReduction (Run Failure Verdict classify unionRun)

abbrev budget : Nat := 200000
abbrev mathlibRevision : String := "56a005855ea17e0b0958f73ec801ae140b0a1679"

def options : Options := ({} : Options).set `maxHeartbeats budget
  |>.set `maxRecDepth 1000 |>.setBool `Elab.async false

structure Attempt where
  strategy : String
  outcome : Run
  proof? : Option Expr := none
  axioms : Array Name := #[]
  detail : String := ""

structure Observation where
  target : Name
  base : Run
  paired : Run
  verdict : Verdict
  attempts : Array Attempt := #[]
  pairAttempts : Array Attempt := #[]
  reason : String := ""
  targetChecked : Bool := false
  structureChecked : Bool := false
  structureClean : Bool := false

def standardAxioms (xs : Array Name) : Bool :=
  xs.all fun n => #[`propext, `Classical.choice, `Quot.sound].contains n

/-- All success is rechecked synchronously at trust level zero. -/
def checkProof (name : Name) (levels : List Name) (type value : Expr) : MetaM (Array Name) := do
  unless !value.hasMVar && !value.hasFVar && !value.hasSorry do
    throwError "search.proof_not_closed"
  addDecl (.thmDecl { name, levelParams := levels, type, value })
  let xs ← collectAxioms name
  unless standardAxioms xs do throwError "search.axioms_outside_standard: {xs}"
  return xs

/-- Deterministic structural search, independent of author proof text. -/
partial def presentation (goal : MVarId) (facts : Array Expr) : MetaM Bool := goal.withContext do
  let saved ← saveState
  for fact in facts do
    let before ← saveState
    try
      let gs ← goal.apply fact
      if ← gs.allM (fun g => g.assumptionCore) then return true
    catch ex =>
      if ex.isRuntime || ex.isInterrupt then throw ex
    before.restore
  let type ← withTransparency .reducible <| whnf (← goal.getType)
  if type.isForall then
    let (_, next) ← goal.intro1
    if ← presentation next facts then return true
  else if type.isAppOfArity ``And 2 then
    let gs ← goal.apply (← mkConstWithFreshMVarLevels ``And.intro)
    if ← gs.allM (fun g => presentation g facts) then return true
  else if type.isAppOfArity ``Iff 2 then
    let gs ← goal.apply (← mkConstWithFreshMVarLevels ``Iff.intro)
    if ← gs.allM (fun g => presentation g facts) then return true
  saved.restore
  return false

/-- Projections and iff directions are facts, never new equivalence licenses. -/
partial def components (fact : Expr) : MetaM (Array Expr) := do
  let type ← whnf (← inferType fact)
  if type.isAppOfArity ``And 2 then
    let a ← mkAppM ``And.left #[fact]
    let b ← mkAppM ``And.right #[fact]
    return #[fact] ++ (← components a) ++ (← components b)
  if type.isAppOfArity ``Iff 2 then
    return #[fact, ← mkAppM ``Iff.mp #[fact], ← mkAppM ``Iff.mpr #[fact]]
  return #[fact]

/-- A discrimination index contains only compiled statement shapes. It is
rebuilt from the isolated environment, not a process-global search cache. -/
abbrev Fact := Name × List Name
structure FactIndex where
  statements : Std.HashMap UInt64 (Array Name) := {}
  projections : LazyDiscrTree Fact := {}

private partial def indexType (index : LazyDiscrTree.PreDiscrTree Fact)
    (name : Name) (path : List Name) (type : Expr) :
    MetaM (LazyDiscrTree.PreDiscrTree Fact) := do
  let entry ← LazyDiscrTree.InitEntry.fromExpr type (name, path)
  let mut index := index.push entry.key entry.entry
  let reduced ← whnf type
  if reduced != type then
    let entry ← LazyDiscrTree.InitEntry.fromExpr reduced (name, path)
    index := index.push entry.key entry.entry
  let type := reduced
  if type.isAppOfArity ``And 2 then
    index ← indexType index name (path ++ [``And.left]) type.appFn!.appArg!
    index ← indexType index name (path ++ [``And.right]) type.appArg!
  if type.isAppOfArity ``Iff 2 then
    let forward ← LazyDiscrTree.InitEntry.fromExpr
      (← mkArrow type.appFn!.appArg! type.appArg!) (name, path ++ [``Iff.mp])
    index := index.push forward.key forward.entry
    let backward ← LazyDiscrTree.InitEntry.fromExpr
      (← mkArrow type.appArg! type.appFn!.appArg!) (name, path ++ [``Iff.mpr])
    index := index.push backward.key backward.entry
  return index

private partial def telescopeBody : Expr → Expr
  | .forallE _ _ body _ => telescopeBody body
  | .mdata _ body => telescopeBody body
  | e => e

/-- The result universe of a compiled type constructor does not depend on its
term arguments. Ambiguous universes retain the ordinary Meta check. -/
private def propositionType (type : Expr) : MetaM Bool := do
  let body := telescopeBody type
  if body.isSort then return false
  if let .const name levels := body.getAppFn then
    let info ← getConstInfo name
    let kind := telescopeBody (info.type.instantiateLevelParams info.levelParams levels)
    if let .sort level := kind then
      if level.isAlwaysZero then return true
      if level.isNeverZero then return false
  isProp type

def factIndex : MetaM FactIndex := do
  let mut index : LazyDiscrTree.PreDiscrTree Fact := {}
  let mut statements : Std.HashMap UInt64 (Array Name) := {}
  let names := (← getEnv).constants.toList.toArray.qsort (fun a b => Name.quickLt a.1 b.1)
  for (name, info) in names do
    if info.isUnsafe then continue
    if name.isInternalDetail && !isPrivateName name then continue
    let initial ← get
    let isStatement ← if info matches .thmInfo _ then pure true else propositionType info.type
    if isStatement then
      let key := info.type.hash
      statements := statements.insert key ((statements[key]?.getD #[]).push name)
      let body := telescopeBody info.type
      let potentialProjection ← match body.getAppFn with
        | .const head _ =>
          let headInfo ← getConstInfo head
          pure <| head == ``And || head == ``Iff || !(headInfo matches .inductInfo _)
        | _ => pure false
      unless potentialProjection do
        set initial
        continue
      index ← forallTelescopeReducing info.type fun _ body => do
        let body ← whnf body
        if body.isAppOfArity ``And 2 || body.isAppOfArity ``Iff 2 then
          indexType index name [] body
        else pure index
    set initial
  return {statements, projections := index.toLazy}

private def factExpr (fact : Fact) : MetaM Expr := do
  let mut e ← mkConstWithFreshMVarLevels fact.1
  for projection in fact.2 do
    let value := e
    e ← forallTelescopeReducing (← inferType value) fun xs _ =>
      mkLambdaFVars xs (← mkAppM projection #[mkAppN value xs])
  return e

partial def structural (goal : MVarId) (extra : Array Name) :
    StateRefT FactIndex MetaM (Array MVarId) := goal.withContext do
  let original ← goal.getType
  let type ← withTransparency .reducible <| whnf original
  for key in #[original.hash, type.hash] do
    for name in (← get).statements[key]?.getD #[] do
      let before ← saveState
      let value ← mkConstWithFreshMVarLevels name
      if ← isDefEq (← inferType value) original then
        goal.assign value
        return #[]
      before.restore
  let mut facts := #[]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      if ← isProp decl.type then facts := facts ++ (← components decl.toExpr)
  for n in extra do
    facts := facts ++ (← components (← mkConstWithFreshMVarLevels n))
  let (hits, index) ← (← get).projections.getMatch type
  modify fun state => {state with projections := index}
  for f in hits.appendResults #[] do facts := facts.push (← factExpr f)
  if ← presentation goal facts then return #[]
  if type.isForall then
    let (_, next) ← goal.intro1
    return ← structural next extra
  if type.isAppOfArity ``And 2 || type.isAppOfArity ``Iff 2 then
    let ctor := if type.isAppOfArity ``And 2 then ``And.intro else ``Iff.intro
    let gs ← goal.apply (← mkConstWithFreshMVarLevels ctor)
    return (← gs.mapM (fun g => structural g extra)).toArray.flatten
  let mut next := goal
  for n in extra do
    let fact ← mkConstWithFreshMVarLevels n
    let factType ← inferType fact
    let g ← next.assert n factType fact
    let (_, g) ← g.intro1
    next := g
  return #[next]

private def exceptionOutcome (ex : Exception) : Run :=
  if ex.isMaxHeartbeat then .incomplete .heartbeat
  else if ex.isInterrupt then .incomplete .cancelled
  else if ex.isRuntime then .incomplete .execution
  else .incomplete .execution

/-- Each call has fresh Core, Meta, Term and tactic state and its own heartbeat
origin. Exceptions are caught outside that state, including resource failures. -/
def attempt (env : Environment) (levels : List Name) (type : Expr)
    (strategy : String) (action : MVarId → MetaM Bool) : IO Attempt := do
  let work : CoreM Attempt := MetaM.run' do
    let goal ← mkFreshExprMVar type
    let ok ← action goal.mvarId!
    if !ok then return { strategy, outcome := .exhausted }
    let proof ← instantiateMVars goal
    let axioms ← checkProof `_searchReduction.proof levels type proof
    return { strategy, outcome := .found, proof? := some proof, axioms }
  let start ← IO.getNumHeartbeats
  let ctx : Core.Context := { fileName := "<R_v1>", fileMap := default, options := options, initHeartbeats := start, maxHeartbeats := budget * 1000 }
  match ← (work.run ctx { env }).toIO' with
  | .ok (result, state) =>
    if state.messages.hasErrors then
      return { strategy, outcome := .incomplete .execution, detail := "elaborator-errors" }
    return result
  | .error ex =>
    return { strategy, outcome := exceptionOutcome ex, detail := (← ex.toMessageData.toString) }

/-- All registered attempts are retained, in priority and stable import order.
No direct invocation of hint (which can admit), native_decide or network. -/
def strategies (env : Environment) : IO (Array (Nat × TSyntax `tactic)) := do
  let xs := Mathlib.Tactic.Hint.hintExtension.getState env
  return (xs.toArray.mapIdx fun i (priority, tac) => (i, priority, tac)).qsort
    (fun a b => a.2.1 > b.2.1 || (a.2.1 == b.2.1 && a.1 < b.1)) |>.map (·.2)

private def combine (xs : Array Attempt) : Run :=
  if xs.isEmpty then .incomplete .missing
  else xs.foldl (fun r a => unionRun r a.outcome) .exhausted

structure Leaf where
  goal : MVarId
  closedType : Expr
  arguments : Array Expr

structure Plan where
  root : Expr
  leaves : Array Leaf
  state : Meta.State

private def makePlan (type : Expr) (index : FactIndex) (extra : Array Name) : MetaM Plan := do
  let root ← mkFreshExprMVar type
  let goals ← (structural root.mvarId! extra).run' index
  let leaves ← goals.mapM fun goal => goal.withContext do
    let mut parameters := #[]
    let mut arguments := #[]
    for decl in ← getLCtx do
      parameters := parameters.push decl.toExpr
      unless decl.isLet do arguments := arguments.push decl.toExpr
    return { goal, closedType := ← mkForallFVars parameters (← goal.getType), arguments : Leaf }
  return {root, leaves, state := ← get}

private def introAll (goal : MVarId) : MetaM MVarId := do
  let mut goal := goal
  while (← withTransparency .reducible <| whnf (← goal.getType)).isForall do
    let (_, next) ← goal.intro1
    goal := next
  return goal

/-- Leaves can close with different strategies. Each leaf/strategy pair starts
from a fresh Core/Meta/Term state with its own default command budget. -/
def search (env : Environment) (levels : List Name) (type : Expr)
    (extra : Array Name) (hints : Array (Nat × TSyntax `tactic)) : IO (Run × Array Attempt) := do
  let context : Core.Context := {fileName := "<R_v1 structure>", fileMap := default, options := options}
  let planResult ← ((MetaM.run' do
    let index ← factIndex
    makePlan type index extra).run
    {context with initHeartbeats := ← IO.getNumHeartbeats} {env}).toIO'
  let plan ← match planResult with
    | .ok (plan, _) => pure plan
    | .error ex =>
      let row : Attempt := {
        strategy := "structure"
        outcome := exceptionOutcome ex
        detail := ← ex.toMessageData.toString }
      return (row.outcome, #[row])
  if plan.leaves.isEmpty then
    let row ← attempt env levels type "presentation/structure" fun goal => do
      let value ← (instantiateMVars plan.root : MetaM Expr).run' {} plan.state
      goal.assign value
      return true
    return (row.outcome, #[row])
  let mut rows : Array Attempt := #[]
  let mut proofs : Array Expr := #[]
  let mut outcome := Run.found
  for h : i in [:plan.leaves.size] do
    let leaf := plan.leaves[i]
    let mut leafRows := #[]
    for (_, tacticSyntax) in hints do
      let row ← attempt env levels leaf.closedType
          s!"leaf[{i}]/{tacticSyntax.raw.reprint.getD (toString tacticSyntax)}" fun goal => do
        let goal ← introAll goal
        let gs ← try
          (Term.withoutErrToSorry <| Tactic.run goal (evalTactic tacticSyntax)).run'
        catch ex =>
          if ex.isRuntime || ex.isInterrupt then throw ex
          return false
        return gs.isEmpty
      leafRows := leafRows.push row
      if row.proof?.isSome then break
    let leafRun := combine leafRows
    if let some success := leafRows.find? (fun row => row.proof?.isSome) then
      proofs := proofs.push success.proof?.get!
    outcome := match outcome, leafRun with
      | .incomplete f, _ => .incomplete f
      | _, .incomplete f => .incomplete f
      | .exhausted, _ | _, .exhausted => .exhausted
      | .found, .found => .found
    -- Leaf proof terms stay internal; only a complete assembled proof may be
    -- exported as a witness for the original statement.
    rows := rows ++ leafRows.map (fun row => {row with proof? := none})
  if outcome != .found then return (outcome, rows)
  let row ← attempt env levels type "kernel/assembled" fun goal => do
    let assembly : MetaM Expr := do
      for h : i in [:plan.leaves.size] do
        plan.leaves[i].goal.assign (mkAppN proofs[i]! plan.leaves[i].arguments)
      instantiateMVars plan.root
    let value ← assembly.run' {} plan.state
    goal.assign value
    return true
  return (row.outcome, rows.push row)

end LeanInformationAudit.SearchReduction
