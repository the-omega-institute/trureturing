import LeanInformationAuditRegAnalysis.SearchReduction.Index
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

/-- A baseline presentation witness contains its actual source and the checked
full-statement conversion, independently of reference-search success. -/
structure PresentationEvidence where
  source : Name
  conversionType : Expr
  conversion : Expr
  proof : Expr
  axioms : Array Name

structure Observation where
  target : Name
  base : Run
  paired : Run
  verdict : Verdict
  attempts : Array Attempt := #[]
  pairAttempts : Array Attempt := #[]
  presentation : Run := .incomplete .undecided
  presentationEvidence? : Option PresentationEvidence := none
  presentationDetail : String := ""
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
      let gs ← withTransparency .reducible <| goal.apply fact
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

private def factExpr (fact : Fact) : MetaM Expr := do
  let mut e ← mkConstWithFreshMVarLevels fact.1
  for projection in fact.2 do
    let value := e
    e ← forallTelescopeReducing (← inferType value) fun xs _ => do
      let projected ← mkAppM projection #[mkAppN value xs]
      mkLambdaFVars xs projected
  return e

partial def structural (goal : MVarId) (extra : Array Name) :
    StateRefT FactIndex MetaM (Array MVarId) := goal.withContext do
  let original ← instantiateMVars (← goal.getType)
  let type ← withTransparency .reducible <| whnf original
  for key in #[original.hash, type.hash] do
    for name in (← statementCandidates key) do
      let before ← (saveState : MetaM Meta.SavedState)
      let value ← mkConstWithFreshMVarLevels name
      if ← isDefEq (← inferType value) original then
        goal.assign value
        return #[]
      (before.restore : MetaM Unit)
  if type.isAppOfArity ``And 2 || type.isAppOfArity ``Iff 2 then
    let ctor := if type.isAppOfArity ``And 2 then ``And.intro else ``Iff.intro
    let gs ← goal.apply (← mkConstWithFreshMVarLevels ctor)
    return (← gs.mapM (fun g => structural g extra)).toArray.flatten
  let originalHead := statementHead original
  let reducedHead := statementHead type
  let heads := if originalHead == reducedHead then #[originalHead]
    else #[originalHead, reducedHead]
  let shape := matcherShape original
  if shape != original then
    for key in heads do
      for name in (← matcherCandidates key) do
        let info ← getConstInfo name
        unless matcherShape info.type == shape do continue
        let before ← (saveState : MetaM Meta.SavedState)
        let value ← mkConstWithFreshMVarLevels name
        let equal ← match Kernel.isDefEq (← getEnv) (← getLCtx) (← inferType value) original with
          | .ok equal => pure equal
          | .error error => throwError "search.matcher_kernel_check: {error.toMessageData (← getOptions)}"
        if equal then
          goal.assign value
          return #[]
        (before.restore : MetaM Unit)
  if type.isForall then
    let (_, next) ← goal.intro1
    return ← structural next extra
  let mut facts := #[]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      if ← isProp decl.type then facts := facts ++ (← components decl.toExpr)
  for n in extra do
    facts := facts ++ (← components (← mkConstWithFreshMVarLevels n))
  if ← presentation goal facts then return #[]
  let hits ← projectionCandidates type
  for f in hits do facts := facts.push (← factExpr f)
  if ← presentation goal facts then return #[]
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

/-- Transport checked terms without references to attempt-local auxiliary declarations. -/
def inlineGenerated (env : Environment) (proof : Expr) : MetaM Expr :=
  Core.transform proof (pre := fun expression => do
    if let .const name levels := expression then
      unless env.contains name do
        let info ← getConstInfo name
        if info.isUnsafe then throwError "search.unsafe_generated_dependency: {name}"
        let some value := info.value? (allowOpaque := true)
          | throwError "search.generated_dependency_without_value: {name}"
        return .visit (value.instantiateLevelParams info.levelParams levels)
    return .continue)

/-- Each call has fresh Core, Meta, Term and tactic state and its own heartbeat
origin. Exceptions are caught outside that state, including resource failures. -/
def attempt (env : Environment) (levels : List Name) (type : Expr)
    (strategy : String) (action : MVarId → MetaM Bool) : IO Attempt := do
  profilePhase s!"attempt {strategy}"
  let work : CoreM Attempt := MetaM.run' do
    let goal ← mkFreshExprMVar type
    let ok ← action goal.mvarId!
    if !ok then return { strategy, outcome := .exhausted }
    let proof ← instantiateMVars goal
    -- Tactics can add auxiliary lemmas to their private environment. Expand
    -- those values before transporting the proof to another attempt state.
    let proof ← inlineGenerated env proof
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

private def makePlan (type : Expr) (index : FactIndex) (extra : Array Name) :
    MetaM (Plan × FactIndex) := do
  let root ← mkFreshExprMVar type
  let (goals, warmed) ← (structural root.mvarId! extra).run index
  let leaves ← goals.mapM fun goal => goal.withContext do
    let mut parameters := #[]
    let mut arguments := #[]
    for decl in ← getLCtx do
      parameters := parameters.push decl.toExpr
      unless decl.isLet do arguments := arguments.push decl.toExpr
    return { goal, closedType := ← mkForallFVars parameters (← goal.getType), arguments : Leaf }
  return ({root, leaves, state := ← get}, warmed)

private def introAll (goal : MVarId) : MetaM MVarId := do
  let mut goal := goal
  while (← withTransparency .reducible <| whnf (← goal.getType)).isForall do
    let (_, next) ← goal.intro1
    goal := next
  return goal

/-- Leaves can close with different strategies. Each leaf/strategy pair starts
from a fresh Core/Meta/Term state with its own default command budget. -/
def searchIndexed (env : Environment) (levels : List Name) (type : Expr)
    (extra : Array Name) (hints : Array (Nat × TSyntax `tactic)) : IO (Run × Array Attempt × Option FactIndex) := do
  let context : Core.Context := {fileName := "<R_v1 structure>", fileMap := default, options := options}
  let planResult ← ((MetaM.run' do
    profilePhase "structure/index"
    let index ← factIndex
    let used := ((← IO.getNumHeartbeats) - (← readThe Core.Context).initHeartbeats) / 1000
    IO.eprintln s!"R_v1 structural index heartbeats: {used}"
    profilePhase "structure/plan"
    let (plan, index) ← makePlan type index extra
    profilePhase "structure/ready"
    return (index, plan)).run
    {context with initHeartbeats := ← IO.getNumHeartbeats} {env}).toIO'
  let (index, plan) ← match planResult with
    | .ok (plan, _) => pure plan
    | .error ex =>
      let row : Attempt := {
        strategy := "structure"
        outcome := exceptionOutcome ex
        detail := ← ex.toMessageData.toString }
      return (row.outcome, #[row], none)
  if plan.leaves.isEmpty then
    let row ← attempt env levels type "presentation/structure" fun goal => do
      let value ← (instantiateMVars plan.root : MetaM Expr).run' {} plan.state
      goal.assign value
      return true
    return (row.outcome, #[row], some index)
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
  if outcome != .found then return (outcome, rows, some index)
  let row ← attempt env levels type "kernel/assembled" fun goal => do
    let assembly : MetaM Expr := do
      for h : i in [:plan.leaves.size] do
        plan.leaves[i].goal.assign (mkAppN proofs[i]! plan.leaves[i].arguments)
      instantiateMVars plan.root
    let value ← assembly.run' {} plan.state
    goal.assign value
    return true
  return (row.outcome, rows.push row, some index)

/-- Callers that only need search outcomes do not retain the statement index. -/
def search (env : Environment) (levels : List Name) (type : Expr)
    (extra : Array Name) (hints : Array (Nat × TSyntax `tactic)) : IO (Run × Array Attempt) := do
  let (outcome, rows, _) ← searchIndexed env levels type extra hints
  return (outcome, rows)

end LeanInformationAudit.SearchReduction
