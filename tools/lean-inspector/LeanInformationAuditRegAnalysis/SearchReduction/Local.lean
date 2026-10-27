import LeanInformationAuditRegAnalysis.SearchReduction.Graph
import LeanInformationAuditRegAnalysis.SearchReduction.Lookup
import LeanInformationAuditRegAnalysis.SearchReduction.Nominators
import LeanInformationAudit.CompiledAxioms
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Declaration dependency extraction and statement-only local reconstruction. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta Elab Tactic

abbrev localBudget : Nat := 200000
abbrev localConfiguration : String := lookupVersion ++ "/analytic-cut-k2/200000"
abbrev sharingConfiguration : String := "statement-exists-and-support"

private def standardClosure (xs : Array Name) : Bool :=
  xs.all (#[`propext, `Classical.choice, `Quot.sound].contains ·)

def checkLocalProof (type proof : Expr) : MetaM Unit := do
  let type ← instantiateMVars type
  let proof ← instantiateMVars proof
  unless !type.hasMVar && !type.hasFVar && !proof.hasMVar && !proof.hasFVar && !proof.hasSorry do
    throwError "graph.unclosed_local_certificate"
  let name ← mkFreshUserName `_declLocal
  let levels := (collectLevelParams {} type).params.toList
  let before ← getEnv
  timeLookup "certificate/kernel" do
    if ← isProp type then
      addDecl (.thmDecl {name, levelParams := levels, type, value := proof})
    else
      addDecl (.defnDecl {
        name, levelParams := levels, type, value := proof,
        hints := .abbrev, safety := .safe})
  let axioms ← timeLookup "certificate/axioms" <| collectAxioms name
  setEnv before
  unless standardClosure axioms do throwError "graph.nonstandard_axioms: {axioms}"

/-- Administrative reduction removes dead lets, beta redexes and discarded
constructor fields. Named author declarations remain opaque dependency nodes. -/
def liveValue (value : Expr) : MetaM Expr := do
  let value ← zetaReduce value
  Meta.transform value (post := fun e => do
    let head := e.getAppFn
    let env ← getEnv
    let reduce := e.isProj || head.isLambda ||
      head.constName?.any (fun n => (env.getProjectionFnInfo? n).isSome)
    if reduce then return .done (← withReducible <| whnf e)
    if let some n := head.constName? then
      if isRecCore (← getEnv) n || isMatcherCore (← getEnv) n then
        return .done (← withReducible <| whnf e)
    return .done e)

def compilerGenerated (env : Environment) (n : Name) : Bool :=
  !allowCompletion env n || isMatcherCore env n || isAuxRecursor env n

private structure ExtractionState where
  vertices : Array GraphVertex := #[]
  edges : Array GraphEdge := #[]
  ids : NameMap Nat := {}
  visiting : NameSet := {}

private abbrev ExtractM := StateRefT ExtractionState MetaM

/-- Ownership is transitive: an equation of a matcher or a nested proof
auxiliary belongs to the same author declaration as its generated parent. -/
private partial def declarationOwner (name : Name) : MetaM Name := do
  if !(compilerGenerated (← getEnv) name || (← isEqnThm name)) then return name
  let mut parent := (← isEqnThm? name).getD name.getPrefix
  while !parent.isAnonymous && !((← getEnv).contains parent) do parent := parent.getPrefix
  if parent.isAnonymous || parent == name then
    throwError "graph.generated_owner_unknown:{name}"
  declarationOwner parent

private def vocabularyKind : ConstantInfo → Bool
  | .inductInfo _ | .ctorInfo _ | .recInfo _ => true
  | _ => false

/-- Generated constants are folded into their nearest existing owner. The
compiler predicates identify auxiliaries; an unowned auxiliary fails closed. -/
private partial def dependencyNames (base : Environment) (owner : Name)
    (info : ConstantInfo) (cache : IO.Ref (NameMap (Array Name)))
    (seen : NameSet := {}) : MetaM (Array Name) := do
  if let some found := (← cache.get).find? info.name then return found
  let (types, _) := CompiledAxioms.declarationDependencyParts info
  let values ← match info.value? (allowOpaque := true) with
    | some value => pure (← liveValue value).getUsedConstants
    | none => pure #[]
  let mut result := #[]
  for dep in types ++ values do
    if dep == owner || seen.contains dep then continue
    let depInfo := ((← getEnv).setExporting false).find? dep
    if !base.contains dep && depInfo.any vocabularyKind then
      result := result ++ (← dependencyNames base owner depInfo.get! cache (seen.insert dep))
    else if !base.contains dep && (compilerGenerated (← getEnv) dep || (← isEqnThm dep)) then
      let some aux := ((← getEnv).setExporting false).find? dep
        | throwError "graph.generated_missing:{dep}"
      let parent ← declarationOwner dep
      let parentInfo := ((← getEnv).setExporting false).find? parent
      if parentInfo.any vocabularyKind then
        result := result ++ (← dependencyNames base owner parentInfo.get! cache
          (seen.insert dep |>.insert parent))
      else if parent != owner then result := result.push parent
      else result := result ++ (← dependencyNames base owner aux cache (seen.insert dep))
    else if !result.contains dep then result := result.push dep
  cache.modify (·.insert info.name result)
  return result

private partial def extractDeclaration (base : Environment) (additions : Array Name)
    (cache : IO.Ref (NameMap (Array Name))) (name : Name) : ExtractM Nat := do
  if (← get).visiting.contains name then throwError "graph.declaration_cycle:{name}"
  if let some id := (← get).ids.find? name then return id
  let info ← getConstInfo name
  let id := (← get).vertices.size
  let seed := base.contains name
  let origin := mkConst name (info.levelParams.map Level.param)
  modify fun s => {s with
    ids := s.ids.insert name id
    visiting := s.visiting.insert name,
    vertices := s.vertices.push {
      id, type := info.type, origin, seed,
      opaqueDecl := !seed, structureSeed := additions.contains name,
      structureProof? := if additions.contains name then some origin else none}}
  unless seed do
    unless (info.value? (allowOpaque := true)).isSome do
      throwError "graph.missing_declaration_body:{name}"
    let deps ← dependencyNames base name info cache
    let mut premises := []
    for dep in deps do premises := premises ++ [← extractDeclaration base additions cache dep]
    modify fun s => {s with edges := s.edges.push {
      conclusion := id, premises := premises.eraseDups, source := some name}}
  modify fun s => {s with visiting := s.visiting.erase name}
  return id

/-- Extraction is one traversal of each live declaration value. No author body
is retained in the graph or supplied to the local reconstructor. -/
def extractGraph (base : Environment) (target : Name)
    (additions : Array Name := #[]) : MetaM ProofGraph := do
  try
    let cache ← IO.mkRef ({} : NameMap (Array Name))
    let (root, state) ← (extractDeclaration base additions cache target).run {}
    return {root, vertices := state.vertices.toList, edges := state.edges.toList}
  catch ex =>
    return {complete := false, issues := [s!"graph.extraction:{← ex.toMessageData.toString}"]}

private partial def injectiveVariables (args telescope : Array Expr) (position : Nat := 0)
    (used : Array Expr := #[]) : MetaM Bool := do
  if position >= args.size then return true
  let value ← instantiateMVars args[position]!
  if value.isMVar then
    for x in telescope do
      if used.contains x then continue
      let saved ← saveState
      if ← withReducible <| isDefEq (← inferType value) (← inferType x) then
        value.mvarId!.assign x
        if ← injectiveVariables args telescope (position + 1) (used.push x) then return true
      saved.restore
    return false
  if value.isFVar && telescope.contains value && !used.contains value then
    return ← injectiveVariables args telescope (position + 1) (used.push value)
  return false

/-- Complete bounded injection matching of statement telescopes. A term or a
repeated variable never qualifies as a binder renaming. -/
def analyticPremise (premise consumer : Expr) : MetaM Bool := do
  let saved ← saveState
  let started ← IO.getNumHeartbeats
  try
    let answer ← withTheReader Core.Context (fun ctx =>
        {ctx with initHeartbeats := started, maxHeartbeats := localBudget * 1000}) do
      let levels := (collectLevelParams {} premise).params.toList
      let premise := premise.instantiateLevelParams levels (← levels.mapM fun _ => mkFreshLevelMVar)
      forallTelescopeReducing consumer fun xs body => do
        let found ← IO.mkRef false
        let mut parts := #[body]
        for x in xs do parts := parts.push (← inferType x)
        for input in parts do
          discard <| Meta.transform input (pre := fun part => do
            if ← found.get then return .done part
            if !(← isProp part) then return .continue
            let before ← saveState
            let (args, _, candidate) ← forallMetaTelescopeReducing premise
            if ← withReducible <| isDefEq candidate part then
              if ← injectiveVariables args xs then found.set true
            before.restore
            return .continue)
        return ← found.get
    saved.restore
    return answer
  catch ex =>
    saved.restore
    throw ex

private def exactLocal (goal : MVarId) (facts : Array Expr) : MetaM Bool := goal.withContext do
  for fact in facts do
    let saved ← saveState
    if ← withReducible <| isDefEq (← inferType fact) (← goal.getType) then
      goal.assign fact
      return true
    saved.restore
  return false

private def tryAssumptions (goal : MVarId) (facts : Array Expr) : MetaM Bool := do
  for fact in facts do
    let saved ← saveState
    try
      let goals ← withReducible <| goal.apply fact {approx := false}
      if ← goals.allM (fun g => exactLocal g facts) then return true
    catch ex =>
      if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
    saved.restore
  return false

private partial def localComponents (fact : Expr) : MetaM (Array Expr) := do
  let type ← whnf (← inferType fact)
  if type.isAppOfArity ``And 2 then
    let left ← mkAppM ``And.left #[fact]
    let right ← mkAppM ``And.right #[fact]
    return #[fact] ++ (← localComponents left) ++ (← localComponents right)
  if type.isAppOfArity ``Iff 2 then
    return #[fact, ← mkAppM ``Iff.mp #[fact], ← mkAppM ``Iff.mpr #[fact]]
  if type.isAppOfArity ``Subtype 2 then
    let property ← mkAppM ``Subtype.property #[fact]
    return #[fact] ++ (← localComponents property)
  return #[fact]

private def eliminateLocal (facts : Array Expr) : MetaM (Array Expr) := do
  return (← facts.mapM localComponents).flatten

private partial def structuralLocal (goal : MVarId) (facts : Array Expr)
    (fuel : Nat := 32) : MetaM Bool := goal.withContext do
  if fuel == 0 then return false
  let type ← withReducible <| whnf (← goal.getType)
  if type.isForall then
    let (fvar, next) ← goal.intro1
    return ← structuralLocal next (facts.push (mkFVar fvar)) (fuel - 1)
  if ← exactLocal goal facts then return true
  let saved ← saveState
  try goal.refl; return true
  catch ex => if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
  saved.restore
  let facts ← eliminateLocal facts
  if ← exactLocal goal facts then return true
  for fact in facts do
    let factType ← withReducible <| whnf (← inferType fact)
    if factType.isAppOfArity ``Exists 2 then
      let before ← saveState
      try
        let (major, next) ← (← goal.assert `_exists factType fact).intro1
        let branches ← next.cases major
        if h : branches.size = 1 then
          let branch := branches[0]'(by omega)
          let available := (facts.filter (· != fact)).map branch.subst.apply
          if ← structuralLocal branch.mvarId (available ++ branch.fields) (fuel - 1) then return true
      catch ex => if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
      before.restore
  let ctor? := if type.isAppOfArity ``And 2 then some ``And.intro
    else if type.isAppOfArity ``Iff 2 then some ``Iff.intro
    else if type.isAppOfArity ``Exists 2 then some ``Exists.intro
    else if type.isAppOfArity ``Subtype 2 then some ``Subtype.mk else none
  if let some ctor := ctor? then
    try
      let goals ← goal.apply (← mkConstWithFreshMVarLevels ctor)
      let obligations ← goals.filterM fun g => g.withContext do isProp (← g.getType)
      if ← obligations.allM (fun g => structuralLocal g facts (fuel - 1)) then
        let proof ← instantiateMVars (mkMVar goal)
        unless proof.hasMVar do return true
    catch ex => if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
    saved.restore
  return ← tryAssumptions goal facts

/-- Fixed procedure order is part of the R identity, independent of calibration. -/
private def solveLocalGoal (goal : MVarId) (facts : Array Expr) : MetaM Bool := do
  for procedure in [:9] do
    let saved ← saveState
    let ok ← try
      if procedure == 0 then structuralLocal goal facts
      else if procedure == 1 then goal.withContext do
        let mut theorems : SimpTheoremsArray := #[]
        for fact in facts do
          let type ← whnf (← inferType fact)
          if type.isAppOfArity ``Eq 3 || type.isAppOfArity ``Iff 2 then
            theorems ← theorems.addTheorem (.fvar fact.fvarId!) fact
        let context ← Simp.mkContext {failIfUnchanged := false} theorems {}
        let (remaining, _) ← simpGoal goal context (simprocs := #[])
        return remaining.isNone
      else goal.withContext do
        let target ← instantiateMVars (← goal.getType)
        if target.hasMVar then return false
        let tac ← match procedure with
          | 2 => `(tactic| omega)
          | 3 => `(tactic| ring)
          | 4 => `(tactic| ring_nf)
          | 5 => do
            let mut names := #[]
            for fact in facts do
              let type ← inferType fact
              if ← isProp type then
                names := names.push (mkIdent (← getFVarLocalDecl fact).userName)
            `(tactic| linarith only [$[$names:term],*])
          | 6 => `(tactic| positivity)
          | 7 => `(tactic| norm_num1)
          | _ =>
            let quantified ← IO.mkRef false
            discard <| Meta.transform target (pre := fun e => do
              if e.isForall || e.isAppOf ``Exists then quantified.set true
              return .continue)
            if ← quantified.get then return false
            `(tactic| decide)
        let goals ← (Term.withoutErrToSorry <| Tactic.run goal (evalTactic tac)).run'
        return goals.isEmpty
    catch ex =>
      if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
      pure false
    if ok then return true
    saved.restore
  return false

structure LocalResult where
  cost : EdgeCost := .unknown
  proof? : Option Expr := none
  detail : String := ""
  used : List Nat := []
  sharedData? : Option Bool := none
  lookup : LookupTrace := {}
  certificate? : Option ObviousCertificate := none
  query : RQuery := .notRun

initialize currentQueryRecords : IO.Ref (List QueryRecord) ← IO.mkRef []

/-- A positive-only boundary cannot manufacture a negative price. A reported
success without a proof is rejected even if its producer sets cost to zero. -/
def certificateOnlyResult (certificate : ObviousCertificate) (result : LocalResult) : LocalResult :=
  if result.cost == .zero && result.proof?.isSome then
    {result with certificate? := some certificate, query := .hit certificate}
  else {result with cost := .unknown, proof? := none, certificate? := none}

private unsafe def solveLookupGoal (table : LookupTable) (goal : MVarId)
    (facts : Array Expr) (tryLocal := true) (name? : Option Name := none) : MetaM LookupTrace := goal.withContext do
  if tryLocal && (← solveLocalGoal goal facts) then return {complete := true}
  let type ← withReducible <| whnf (← goal.getType)
  if type.isForall then
    let (fvar, next) ← goal.intro1
    return ← solveLookupGoal table next (facts.push (mkFVar fvar)) true name?
  if type.isAppOfArity ``And 2 || type.isAppOfArity ``Iff 2 then
    let saved ← saveState
    let ctor := if type.isAppOfArity ``And 2 then ``And.intro else ``Iff.intro
    let goals ← goal.apply (← mkConstWithFreshMVarLevels ctor)
    let mut trace : LookupTrace := {complete := true}
    let mut solved := true
    for next in goals do
      let leaf ← solveLookupGoal table next facts true name?
      trace := mergeLookupTrace trace leaf
      unless ← next.isAssigned do solved := false
    if solved then return trace
    -- A split query is part of the same R success space as its parent.
    -- Once one child enumeration is incomplete, falling back to the parent
    -- query would erase that residual and could turn unknown into NoHit.
    if !trace.complete then
      let mut failures := trace.failures.push "B1:split-incomplete"
      if (← IO.getEnv "SEARCH_REDUCTION_B1_COMPARE") == some "1" then
        let splitState ← saveState
        let heartbeats ← IO.getNumHeartbeats
        let budget ← table.budget?.mapM (·.get)
        try
          saved.restore
          let projected ← eliminateLocal facts
          let parent ← if let some name := name? then
              lookupNamedLeaf table name goal (fun next => exactLocal next projected)
                (fun next => solveLocalGoal next facts)
            else
              lookupLeaf table goal (fun next => exactLocal next projected)
                (fun next => solveLocalGoal next facts)
          let price := if parent.source?.isSome then "zero"
            else if parent.complete then "one" else "unknown"
          failures := failures.push s!"B1:parent={price}"
          emitLookupRecord s!"LOOKUP_B1_COMPARISON parent={price} split=unknown"
        finally
          splitState.restore
          if let some ref := table.budget? then
            if let some state := budget then ref.set state
          IO.setNumHeartbeats heartbeats
      saved.restore
      return {trace with source? := none, failures}
    saved.restore
  let projected ← eliminateLocal facts
  if let some name := name? then
    return ← lookupNamedLeaf table name goal (fun next => exactLocal next projected)
      (fun next => solveLocalGoal next facts)
  lookupLeaf table goal (fun next => exactLocal next projected)
    (fun next => solveLocalGoal next facts)

/-- Verdict-free fixed-stride cost sampling over the primary implication
index. The historical star page is excluded from production measurement. -/
unsafe def telemetryLookupCosts (table : LookupTable) (type : Expr) : MetaM Unit := do
  unless (← IO.getEnv "SEARCH_REDUCTION_TELEMETRY").isSome do
    throwError "lookup.telemetry_flag_required"
  let original ← saveState
  if let some budget := table.budget? then budget.set {}
  let root ← mkFreshExprMVar type
  let mut goal := root.mvarId!
  let mut facts := #[]
  while (← goal.withContext <| withReducible <| whnf (← goal.getType)).isForall do
    let (fvar, next) ← goal.intro1
    facts := facts.push (mkFVar fvar)
    goal := next
  discard <| goal.withContext <| lookupLeafPass table goal
    (fun next => exactLocal next facts) (fun next => solveLocalGoal next facts)
  original.restore
  set original.meta
  modifyThe Core.State fun state => {state with cache := original.core.cache}
  if let some close := table.close? then close

private def withFacts {α : Type} (types : List Expr)
    (action : Array Expr → MetaM α) : MetaM α := do
  let rec go (remaining : List Expr) (facts : Array Expr) : MetaM α := do
    match remaining with
    | [] => action facts
    | type :: rest => withLocalDeclD (Name.num `_premise facts.size) type (fun fact => go rest (facts.push fact))
  go types #[]

/-- A branch boundary catches resource limits and interrupts at the underlying
EIO layer. Core's ordinary try/catch deliberately rethrows these exceptions. -/
private def catchBranch {α : Type} (action : MetaM α)
    (handler : Exception → MetaM α) : MetaM α :=
  controlAt CoreM fun runInBase => fun ctx state => do
    try runInBase action ctx state
    catch ex => runInBase (handler ex) ctx state

/-- Each route receives the same independent budget and exports only a closed
certificate. Failed metavariables, caches and messages cannot reach its peer. -/
def boundedRebuildBranch (action : MetaM LocalResult)
    (budget? : Option (IO.Ref LookupBudgetState) := none) : MetaM LocalResult := do
  let original ← saveState
  resetCache
  modifyThe Core.State fun s => {s with cache := {}}
  if let some budget := budget? then budget.set {}
  let started ← IO.getNumHeartbeats
  let nanos ← IO.monoNanosNow
  let result ← catchBranch
    (withTheReader Core.Context (fun ctx =>
      {ctx with initHeartbeats := started, maxHeartbeats := if budget?.isSome then 0 else localBudget * 1000}) do
        let result ← action
        checkSystem "lookup.search-branch"
        return result)
    (fun ex => do
      if ex.isMaxHeartbeat then
        let preparation := (← budget?.mapM (·.get)).any
          (·.preparation >= lookupPreparationBudget * 1000)
        let reason := if preparation then "candidate-preparation-limit"
          else if budget?.isSome then "lookup-enclosing-heartbeat"
          else "local-closure-heartbeat"
        return {detail := reason, query := .fault reason}
      if ex.isInterrupt then return {detail := "cancelled", query := .fault "cancelled"}
      if ex.isRuntime then return {detail := "runtime-limit", query := .fault "runtime-limit"}
      let reason := s!"execution:{← ex.toMessageData.toString}"
      return {detail := reason, query := .fault reason})
  let search := (← IO.getNumHeartbeats) - started
  let elapsed := (← IO.monoNanosNow) - nanos
  let preparation := (← budget?.mapM (·.get)).getD {}
  emitLookupRecord s!"LOOKUP_BUDGET {Json.mkObj [
    ("finished_monotonic_ms", toJson (← IO.monoMsNow)),
    ("search_internal_heartbeats", toJson search),
    ("preparation_internal_heartbeats", toJson preparation.preparation),
    ("search_limit", toJson localBudget), ("preparation_limit", toJson lookupPreparationBudget),
    ("coverage_internal_heartbeats", toJson preparation.coverage),
    ("coverage_limit", toJson lookupCoverageBudget),
    ("preparation_ns", toJson preparation.preparationNs),
    ("search_ns", toJson (elapsed - preparation.preparationNs)),
    ("cost", toJson (reprStr result.cost)), ("detail", toJson result.detail)] |>.compress}"
  original.restore
  set original.meta
  modifyThe Core.State fun s => {s with cache := original.core.cache}
  return result

/-- A success in either route wins. Negative evidence requires both routes to
finish normally; timeout in one route never becomes a one-price edge. -/
def independentRebuild (localRoute lookup : MetaM LocalResult)
    (budget? : Option (IO.Ref LookupBudgetState) := none) : MetaM LocalResult := do
  let started ← IO.monoMsNow
  let old ← boundedRebuildBranch localRoute
  lookupPhase s!"rebuild/local ms={(← IO.monoMsNow) - started} cost={reprStr old.cost}"
  if old.cost == .zero then return old
  let lookupStart ← IO.monoMsNow
  let found ← boundedRebuildBranch lookup budget?
  lookupPhase s!"rebuild/lookup ms={(← IO.monoMsNow) - lookupStart} cost={reprStr found.cost} detail={found.detail}"
  if found.cost == .zero then return found
  return {found with
    cost := if old.cost == .one && found.cost == .one &&
      old.query.price == some 1 && found.query.price == some 1 then .one else .unknown
    query := if old.cost == .one then found.query else .fault s!"local-branch:{old.detail}"
    detail := s!"local={old.detail};lookup={found.detail}"}

/-- Only statement types enter R. The successful lambda retains precisely its
used premise binders, so zero edges carry their actual premises. -/
private unsafe def rebuildRoute (target : Expr) (types : List Expr)
    (lookup? : Option LookupTable) (certificate? : Option ObviousCertificate := none) : MetaM LocalResult := do
  let originalEnv ← getEnv
  let finish (proof : Expr) : MetaM Expr := do
    if let some exportProof := lookup?.bind (·.finish?) then
      exportProof originalEnv proof
    else pure proof
  withFacts types fun facts => do
    let root ← mkFreshExprMVar target
    let mut goal := root.mvarId!
    let mut available := facts
    while (← goal.withContext <| withReducible <| whnf (← goal.getType)).isForall do
      let (fvar, next) ← goal.intro1
      available := available.push (mkFVar fvar)
      goal := next
    let mut membershipTrace : LookupTrace := {complete := true}
    if let some table := lookup? then
        let exactRoot ← mkFreshExprMVar target
        let exactTrace ← match certificate? with
          | some (.member name) => lookupNamedMember table name exactRoot.mvarId!
          | some _ => pure {complete := true}
          | none => lookupExact table exactRoot.mvarId!
        membershipTrace := exactTrace
        if exactTrace.source?.isSome then
          let proof ← finish (← instantiateMVars exactRoot)
          withEnv originalEnv <| checkLocalProof target proof
          return {
            cost := .zero, proof? := some proof, lookup := exactTrace,
            certificate? := exactTrace.source?.map ObviousCertificate.member,
            query := .hit (.member exactTrace.source?.get!),
            detail := s!"kernel-checked-lookup:{exactTrace.source?}"}
    if certificate?.any (fun c => match c with | .member _ => true | _ => false) then
      return {detail := "certificate.member_not_verified"}
    let trace ← if let some table := lookup? then
        goal.withContext (solveLookupGoal table goal available false
          (certificate?.bind fun c => match c with | .lookup n => some n | _ => none))
      else do
        discard <| goal.withContext (solveLocalGoal goal available)
        pure {complete := true}
    let trace := mergeLookupTrace membershipTrace trace
    if let some (.lookup name) := certificate? then
      unless trace.source? == some name do
        return {detail := "certificate.lookup_name_not_used_or_out_of_scope"}
    unless ← goal.isAssigned do
      let query := if lookup?.isSome then trace.terminal else RQuery.miss .exhaustive
      return {
        cost := query.cost, query, lookup := trace
        detail := if trace.complete then
          if lookup?.isSome then
            s!"normal-exhaustion/lookup-complete:pages={trace.pages},visited={trace.visited},attempted={trace.attempted},unloaded_checked={trace.unloaded}"
          else "normal-exhaustion/local-only"
          else s!"lookup-incomplete-basis:pages={trace.pages},missing={trace.missing.take 8},missing_count={trace.missing.size},reasons={trace.failures}"}
    let proof ← instantiateMVars root
    unless !proof.hasMVar do return {detail := "unclosed-reconstruction"}
    let used := facts.toList.zipIdx.filterMap fun (fact, i) =>
      if proof.containsFVar fact.fvarId! then some i else none
    let selected := used.toArray.map (facts[·]!)
    let certificate ← finish (← mkLambdaFVars selected proof)
    let certificateType ← mkForallFVars selected target
    withEnv originalEnv <| checkLocalProof certificateType certificate
    let obvious := trace.source?.map ObviousCertificate.lookup |>.getD .close
    return {
      cost := .zero, proof? := some certificate, used, lookup := trace,
      certificate? := some obvious, query := .hit obvious,
      detail := if let some name := trace.source? then s!"kernel-checked-lookup:{name}"
        else "kernel-checked-statement"}

/-- The replayer constructs the complete target and Γ; the author supplies
only a frozen constructor and optionally one untrusted name. Failed replay,
including a capped candidate, can never produce cost one. -/
unsafe def replayCertificate (target : Expr) (types : List Expr)
    (certificate : ObviousCertificate) (lookup? : Option LookupTable := none) : MetaM LocalResult := do
  let result ← match certificate with
    | .close => boundedRebuildBranch (rebuildRoute target types none (some certificate))
    | _ =>
      if let some table := lookup? then
        boundedRebuildBranch (rebuildRoute target types (some table) (some certificate)) table.budget?
      else pure {detail := "certificate.lookup_unavailable"}
  return certificateOnlyResult certificate result

/-- Typed answers are scoped to exact target vocabulary, protected basis data
and the explicit R version. JSON projections never enter this cache. -/
structure LocalMemoAnswer where
  identity : String
  result : LocalResult

private initialize localMemoContext : IO.Ref String ← IO.mkRef ""
private initialize certificateOnlyAnswers : IO.Ref (Std.HashMap String LocalResult) ← IO.mkRef {}
private initialize localMemoAnswers : IO.Ref (Std.HashMap String LocalResult) ← IO.mkRef {}
private initialize localMemoRegions : IO.Ref (Array CompactedRegion) ← IO.mkRef #[]

def localMemoEnabled : IO Bool := do
  return (← IO.getEnv "SEARCH_REDUCTION_MEMO") != some "0"

private def prepareLocalMemo (table : LookupTable) (graph : ProofGraph) : MetaM Unit := do
  localMemoAnswers.set {}
  certificateOnlyAnswers.set {}
  localMemoContext.set ""
  unless ← localMemoEnabled do return
  let env ← getEnv
  let mut todo := graph.vertices.foldl (fun names v => names ++ v.type.getUsedConstants) #[]
  let mut seen : NameSet := {}
  let mut vocabulary : Array (Name × Expr × Option Expr) := #[]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name || (table.environment.setExporting false).contains name then continue
    seen := seen.insert name
    let some info := (env.setExporting false).find? name | continue
    vocabulary := vocabulary.push (name, info.type, info.value? (allowOpaque := true))
    for dependency in info.getUsedConstantsAsSet do todo := todo.push dependency
  let root := graph.vertices.find? (·.id == graph.root)
  let identity := reprStr (lookupExecutionVersion, localConfiguration,
    table.disk?.map (fun d =>
      ((toJson d.header).compress, (toJson d.membership?).compress, d.excluded)),
    table.complete, table.enabled, table.environment.header.moduleNames, table.implicationModules?,
    root.bind (·.origin.constName?), graph.vertices.map (·.type), vocabulary,
    ← IO.getEnv "SEARCH_REDUCTION_RESUME_INPUTS")
  localMemoContext.set identity

private def checkMemoProof (target : Expr) (types : List Expr)
    (result : LocalResult) : MetaM Unit := do
  if result.cost != .zero then return
  let some proof := result.proof? | throwError "lookup.memo_missing_certificate"
  withFacts types fun facts => do
    let mut selected := #[]
    for index in result.used do
      let some fact := facts[index]? | throwError "lookup.memo_premise_mismatch"
      selected := selected.push fact
    let expected ← mkForallFVars selected target
    checkLocalProof expected proof

private unsafe def memoizedLocalRebuild (target : Expr) (types : List Expr)
    (action : MetaM LocalResult) : MetaM LocalResult := do
  let context ← localMemoContext.get
  if context.isEmpty || target.hasFVar || target.hasMVar ||
      types.any (fun type => type.hasFVar || type.hasMVar) then return ← action
  let identity := context ++ reprStr (target, types)
  if let some result := (← localMemoAnswers.get)[identity]? then
    checkMemoProof target types result
    lookupPhase s!"lookup/memo hit=round query={hash identity}"
    return result
  let directory := (← IO.getEnv "SEARCH_REDUCTION_QUERY_CACHE").getD
    "build/lean-inspector/search-reduction-query-cache"
  let path := (System.FilePath.mk directory) / s!"target-{hash context}" / s!"query-{hash identity}.pickle"
  if !directory.isEmpty && (← path.pathExists) then
    try
      let (record, region) ← unpickle LocalMemoAnswer path
      localMemoRegions.modify (·.push region)
      unless record.identity == identity do throwError "lookup.memo_input_mismatch"
      checkMemoProof target types record.result
      localMemoAnswers.modify (·.insert identity record.result)
      lookupPhase s!"lookup/memo hit=disk query={hash identity}"
      return record.result
    catch ex =>
      if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
      emitLookupRecord s!"LOOKUP_MEMO_REJECTED query={hash identity} reason={← ex.toMessageData.toString}"
  lookupPhase s!"lookup/memo miss query={hash identity}"
  let result ← action
  checkMemoProof target types result
  localMemoAnswers.modify (·.insert identity result)
  if !directory.isEmpty then
    IO.FS.createDirAll path.parent.get!
    let temporary := path.addExtension "tmp"
    pickle temporary ({identity, result} : LocalMemoAnswer)
    IO.FS.rename temporary path
  return result

unsafe def localRebuild (target : Expr) (types : List Expr := [])
    (lookup? : Option LookupTable := none) (role : String := "R") : MetaM LocalResult := do
  let finish (result : LocalResult) : MetaM LocalResult := do
    currentQueryRecords.modify (· ++ [{
      role, target := target.hash,
      premises := types.map Expr.hash, terminal := result.query,
      encounteredSearchKappa := result.lookup.searchKappa,
      encounteredCoveragePrefixG := result.lookup.coveragePrefixG,
      encounteredFaults := result.lookup.faults}])
    emitLookupRecord s!"R_QUERY {Json.mkObj [
      ("role", toJson role), ("target_hash", toJson target.hash),
      ("terminal", toJson (reprStr result.query)),
      ("v18_price", toJson result.query.priceV18),
      ("v19_price", toJson result.query.price),
      ("guard_run", toJson (reprStr result.query.guardRun))] |>.compress}"
    return result
  let result ← memoizedLocalRebuild target types do
    let localRoute := rebuildRoute target types none
    if let some table := lookup? then
      if table.enabled then
        try
          return ← independentRebuild localRoute (rebuildRoute target types (some table)) table.budget?
        finally
          if let some close := table.close? then close
    boundedRebuildBranch localRoute
  if result.cost != .zero then return ← finish result
  let some certificate := result.certificate?
    | return ← finish {
        detail := "certificate.R_hit_has_no_name_only_export",
        query := .fault "certificate.R_hit_has_no_name_only_export"}
  let checked ← replayCertificate target types certificate lookup?
  if checked.cost != .zero then
    return ← finish {
      detail := s!"certificate.R_export_replay_failed:{certificate.render}",
      query := .fault "certificate.R_export_replay_failed"}
  certificateNominations.modify (·.push ⟨certificate, "R-hit"⟩)
  return ← finish {checked with lookup := result.lookup}

/-- Positive-only front end. Empty nominations and failed verification remain
unknown; neither path invokes primary-index enumeration. -/
private unsafe def certifyLocalUncached (target : Expr) (types : List Expr := [])
    (lookup? : Option LookupTable := none)
    (nominations : Array ObviousCertificate := #[]) : MetaM LocalResult := do
  let closed ← replayCertificate target types .close lookup?
  if closed.cost == .zero then return closed
  let members ← if let some table := lookup? then
    try memberCertificateNames table target catch _ => pure #[]
    else pure #[]
  let pool ← certificateNominations.get
  let submitted := nominationCertificates (pool ++
    (nominations.map fun c => ⟨c, "explicit"⟩))
  let automatic := nominationCertificates
    (members.map fun name => ⟨.member name, "alpha-membership"⟩)
  let candidates := submitted ++ automatic.filter (fun c => !submitted.contains c)
  for candidate in candidates do
    match candidate with
    | .close => continue
    | .member name => if !members.contains name then continue
    | .lookup _ => pure ()
    let checked ← replayCertificate target types candidate lookup?
    if checked.cost == .zero then return checked
  return {detail := "certificate.not_found;not_a_negative"}

/-- Positive-only query answers are separate from completed R answers. Pool
identity prevents a failed nomination set hiding later registered evidence. -/
unsafe def certifyLocal (target : Expr) (types : List Expr := [])
    (lookup? : Option LookupTable := none) (owner? : Option Name := none) : MetaM LocalResult := do
  let global ← certificateNominations.get
  let edgePool := (← edgeCertificateNominations.get).filterMap fun (owner, nomination) =>
    if some owner == owner? then some nomination else none
  certificateNominations.set (global ++ edgePool)
  try
    let key := reprStr (target, types, nominationCertificates (global ++ edgePool))
    if let some result := (← certificateOnlyAnswers.get)[key]? then
      checkMemoProof target types result
      return result
    let result ← certifyLocalUncached target types lookup?
    certificateOnlyAnswers.modify (·.insert key result)
    return result
  finally certificateNominations.set global

private def vertex (graph : ProofGraph) (id : Nat) : GraphVertex :=
  (graph.vertices.find? (·.id == id)).getD default

/-- Only existential data choices enter this syntactic observation. A shared
parameter already supplied by the caller is not an unresolved witness. -/
private partial def sharedWitnessSupport (type : Expr) (choices : Array Expr := #[]) :
    MetaM Bool := do
  let type ← withReducible <| whnf type
  if type.isForall then
    return ← forallTelescopeReducing type fun _ body => sharedWitnessSupport body choices
  if type.isAppOfArity ``Exists 2 then
    let domain := type.getArg! 0
    let predicate := type.getArg! 1
    return ← withLocalDeclNoLocalInstanceUpdate `_sharingWitness .default domain fun x => do
      let choices := if ← isProp domain then choices else choices.push x
      sharedWitnessSupport (mkApp predicate x) choices
  if type.isAppOfArity ``And 2 || type.isAppOfArity ``Or 2 then
    let left := type.getArg! 0
    let right := type.getArg! 1
    if type.isAppOfArity ``And 2 && choices.any (fun x =>
        left.containsFVar x.fvarId! && right.containsFVar x.fvarId!) then return true
    if ← sharedWitnessSupport left choices then return true
    return ← sharedWitnessSupport right choices
  return false

/-- Sharing is an observation with its own bound; failure cannot change prices
or the mathematical completeness of the declaration graph. -/
private def statementSharing (type : Expr) : MetaM (Except String Bool) := do
  let started ← IO.getNumHeartbeats
  try
    return .ok (← withTheReader Core.Context (fun ctx =>
      {ctx with initHeartbeats := started, maxHeartbeats := localBudget * 1000}) do
        sharedWitnessSupport type)
  catch ex => return .error (← ex.toMessageData.toString)

/-- Type classification is shared by both arms and the given-premise ablation. -/
private def annotateGraph (graph : ProofGraph) : MetaM ProofGraph := do
  let mut edges := []
  let mut graph := graph
  for edge in graph.edges do
    let mut edge := edge
    match ← statementSharing (vertex graph edge.conclusion).type with
    | .ok shared => edge := {edge with sharedData? := some shared}
    | .error detail =>
      graph := {graph with issues :=
        s!"graph.shared_data:{edge.source}:{detail}" :: graph.issues}
    let started ← IO.getNumHeartbeats
    try
      let analytic ← withTheReader Core.Context (fun ctx =>
          {ctx with initHeartbeats := started, maxHeartbeats := localBudget * 1000}) do
        edge.premises.filterM fun p =>
          analyticPremise (vertex graph p).type (vertex graph edge.conclusion).type
      edge := {edge with analytic}
    catch ex =>
      let issue := s!"graph.analytic:{edge.source}:{← ex.toMessageData.toString}"
      if edge.window != 1 then
        graph := {graph with issues := issue :: graph.issues}
        continue
      graph := {graph with complete := false, issues := issue :: graph.issues}
    edges := edges ++ [edge]
  return {graph with edges}

/-- Same price function in each arm; only the seed flag changes. -/
unsafe def priceGraph (graph : ProofGraph) (paired := false) (allGiven := false)
    (lookup? : Option LookupTable := none) : MetaM ProofGraph := do
  let mut edges := []
  let seeds := (graph.vertices.filter (fun v =>
    v.seed || (paired && v.structureSeed && !v.targetPart))).map (·.id)
  for edge in graph.edges do
    let available := if allGiven then edge.premises else statementPremises edge seeds
    let analytic := edge.analytic
    let result ← certifyLocal (vertex graph edge.conclusion).type
      (available.map (vertex graph · |>.type)) lookup? edge.source
    let result := if edge.window != 1 && result.cost != .zero then
      {result with cost := .unknown} else result
    let used := result.used.map (available[·]!)
    let edge := if allGiven then
        if paired then {edge with pairedVisibleCost := result.cost, pairedGivenUsedPremises := used}
        else {edge with visibleCost := result.cost, givenUsedPremises := used}
      else if paired then {edge with
        pairedCost := result.cost, pairedZeroProof := result.proof?, pairedUsedPremises := used,
        pairedCertificate? := result.certificate?, pairedQuery := result.query}
      else {edge with
        cost := result.cost, zeroProof := result.proof?, usedPremises := used,
        certificate? := result.certificate?,
        analytic, detail := result.detail, query := result.query}
    let edge := if allGiven then edge else
      match result.certificate?, result.proof? with
      | some certificate, some proof => attachCertificate edge paired certificate proof used
      | _, _ => edge
    edges := edges ++ [edge]
  return {graph with edges}

def armSeeds (graph : ProofGraph) (paired : Bool) : List Nat :=
  (graph.vertices.filter (fun v => v.seed || (paired && v.structureSeed && !v.targetPart))).map (·.id)

def armGraph (graph : ProofGraph) (paired allGiven : Bool) (lower := false) : ProofGraph :=
  {graph with edges := (graph.edges.filter (fun edge => edgeActive edge paired allGiven)).map fun edge =>
    let cost := if allGiven then (if paired then edge.pairedVisibleCost else edge.visibleCost)
      else if paired then edge.pairedCost else edge.cost
    {edge with cost, premises := if lower && cost == .unknown then [] else if cost == .zero then
      (if allGiven then
        (if paired then edge.pairedGivenUsedPremises else edge.givenUsedPremises)
       else if paired then edge.pairedUsedPremises else edge.usedPremises) else edge.premises}}

unsafe def rootProbe (graph : ProofGraph) (paired := false)
    (lookup? : Option LookupTable := none) (negative := false) : MetaM ProbeResult := do
  let seeds := armSeeds graph paired
  let result ← if negative && !paired then
      localRebuild (vertex graph graph.root).type (seeds.map (vertex graph · |>.type)) lookup? "baseline-root"
    else
      certifyLocal (vertex graph graph.root).type (seeds.map (vertex graph · |>.type))
        lookup? (vertex graph graph.root).origin.constName?
  let outcome := match result.cost with
    | .zero => Run.found | .one => .exhausted | .unknown => .incomplete .undecided
  return {
    outcome, checked := result.proof?.isSome, premises := result.used.map (seeds[·]!),
    proof? := result.proof?, certificate? := result.certificate?, detail := result.detail,
    query := result.query}

/-- Only zero certificates and seed constants are assembled, never author
nonseed values. The backpointers come from the same table as the reported DP. -/
def assembleZero (graph : ProofGraph) (paired := false) : MetaM (Option Expr) := do
  let arm := armGraph graph paired false
  let seeds := armSeeds graph paired
  let table := dpTable arm costUpper seeds
  let rec go (fuel id : Nat) : MetaM (Option Expr) := do
    if h : fuel = 0 then return ← throwError "graph.assembly_fuel:{id}"
    let v := vertex graph id
    if v.seed then return some v.origin
    if paired && v.structureSeed && !v.targetPart then return v.structureProof?
    let some index := (table[id]?.getD {}).edge?
      | throwError "graph.assembly_missing_backpointer:{id}"
    let some edge := arm.edges[index]?
      | throwError "graph.assembly_missing_edge:{id}:{index}"
    let some schema := if paired then edge.pairedZeroProof else edge.zeroProof
      | throwError "graph.assembly_missing_certificate:{id}:{index}"
    let mut arguments := #[]
    for p in edge.premises do
      let some proof ← go (fuel - 1) p | return none
      arguments := arguments.push proof
    return some (mkAppN schema arguments)
  termination_by fuel
  decreasing_by omega
  try
    let some proof ← go (graph.vertices.length + 1) graph.root | return none
    checkLocalProof (vertex graph graph.root).type proof
    return some proof
  catch ex =>
    logInfo m!"GRAPH_ASSEMBLY_INCOMPLETE paired={paired}: {← ex.toMessageData.toString}"
    return none

/-- Lower bounds allow an unknown successful certificate to discard any
premises. Upper bounds retain the author's known route. -/
def armInterval (graph : ProofGraph) (paired := false) (allGiven := false)
    (id? : Option Nat := none) : Interval :=
  let seeds := armSeeds graph paired
  let id := id?.getD graph.root
  ⟨depth (armGraph graph paired allGiven true) costLower seeds id,
   depth (armGraph graph paired allGiven) costUpper seeds id⟩

private def addRootProbe (graph : ProofGraph) (probe : ProbeResult) (paired : Bool) : ProofGraph :=
  if !probe.checked then graph else
  let actual := probe.premises
  {graph with edges := graph.edges ++ [{
    conclusion := graph.root, premises := actual, window := 0,
    cost := if paired then .unknown else .zero, pairedCost := .zero,
    visibleCost := .zero, pairedVisibleCost := .zero,
    usedPremises := if paired then [] else actual, pairedUsedPremises := actual,
    givenUsedPremises := if paired then [] else actual, pairedGivenUsedPremises := actual,
    zeroProof := if paired then none else probe.proof?, pairedZeroProof := probe.proof?,
    certificate? := if paired then none else probe.certificate?,
    pairedCertificate? := probe.certificate?,
    query := if paired then .notRun else probe.query, pairedQuery := probe.query,
    sharedData? := (graph.edges.find? (·.conclusion == graph.root)).bind (·.sharedData?),
    detail := if paired then "paired-root-certificate" else "baseline-root-certificate"}]}

/-- Unknown author edges selected by the optimistic lower-bound DP. The
traversal retains graph edge indices and visits shared premises once. -/
private def lowerUnknownPath (graph : ProofGraph) : List Nat := Id.run do
  let arm := armGraph graph false false true
  let seeds := armSeeds graph false
  let table := dpTable arm costLower seeds
  let mut pending := [graph.root]
  let mut seen := []
  let mut result := []
  for _ in [:graph.vertices.length + (graph.edges.map (·.premises.length)).sum + 1] do
    let v :: rest := pending | break
    pending := rest
    if seen.contains v || seeds.contains v then continue
    seen := v :: seen
    if let some index := (table[v]?.getD {}).edge? then
      if let some edge := arm.edges[index]? then
        if edge.cost == .unknown then
          -- armGraph filters inactive shortcuts, so recover the original edge.
          if let some original := graph.edges.zipIdx.find? (fun (e, _) =>
              e.conclusion == edge.conclusion && e.window == edge.window && e.source == edge.source) then
            result := result ++ [original.2]
        pending := edge.premises ++ pending
  return result.eraseDups

/-- Only a decisive gap can request full R, and only in the baseline arm.
A failed or capped request is tried once and remains unknown. -/
private unsafe def refineBaseline (initial : ProofGraph) (lookup? : Option LookupTable)
    (initialProbe : ProbeResult) : MetaM (ProofGraph × ProbeResult × Nat) := do
  let mut graph := initial
  let mut probe := initialProbe
  let mut calls := 0
  let mut tried := []
  let exhaustive := (← IO.getEnv "SEARCH_REDUCTION_FULL_EVAL") == some "1"
  if exhaustive || better (armInterval graph true).upper (armInterval graph).upper then
    probe ← rootProbe graph false lookup? true
    calls := calls + 1
    graph := addRootProbe graph probe false
  for _ in [:initial.edges.length] do
    let base := armInterval graph
    let paired := armInterval graph true
    if !exhaustive && (!better paired.upper base.upper ||
        (strictDrop base paired && probe.outcome == .exhausted)) then break
    let witnesses := graph.edges.zipIdx.filterMap fun (edge, i) =>
      if edge.window == 1 && edge.cost == .unknown && edge.pairedCost == .zero then some i else none
    let candidates := if exhaustive then graph.edges.zipIdx.filterMap fun (edge, i) =>
        if edge.window == 1 && edge.cost == .unknown then some i else none
      else (witnesses ++ lowerUnknownPath graph).eraseDups
    let some index := candidates.find? (fun i => !tried.contains i) | break
    tried := index :: tried
    let some edge := graph.edges[index]? | continue
    let available := statementPremises edge (armSeeds graph false)
    let result ← localRebuild (vertex graph edge.conclusion).type
      (available.map (vertex graph · |>.type)) lookup? s!"author-edge:{edge.source}:{edge.conclusion}"
    calls := calls + 1
    let used := result.used.map (available[·]!)
    let edge := {edge with
      cost := result.cost, zeroProof := result.proof?,
      certificate? := result.certificate?, usedPremises := used, detail := result.detail,
      query := result.query}
    let edge := if result.cost == .zero then {edge with
      pairedCost := .zero, pairedZeroProof := result.proof?, pairedUsedPremises := used,
      pairedCertificate? := result.certificate?} else edge
    let edge := match result.certificate?, result.proof? with
      | some certificate, some proof =>
        attachCertificate (attachCertificate edge false certificate proof used)
          true certificate proof used
      | _, _ => edge
    graph := {graph with edges := graph.edges.set index edge}
  return (graph, probe, calls)

/-- Certificates are checked first in both arms. Full negative R is reserved
for a possible strict drop. Paired queries never request negative evidence. -/
unsafe def evaluateGraph (raw : ProofGraph) (lookup? : Option LookupTable := none)
    (nominations : Array CertificateNomination := #[])
    (bindings : Array (Name × CertificateNomination) := #[])
    (positiveEligible : Bool := true) : MetaM GraphReading := do
  currentQueryRecords.set []
  if raw.vertices.isEmpty then return {graph := raw}
  let mut raw := raw
  let enabled := (← IO.getEnv "SEARCH_REDUCTION_LOOKUP") != some "0"
  let table ← resolveLookupTable (lookup?.getD {environment := ← getEnv, enabled})
  prepareLocalMemo table raw
  let previousPool ← certificateNominations.get
  let previousBindings ← edgeCertificateNominations.get
  certificateNominations.set nominations
  edgeCertificateNominations.set bindings
  try
    let lookup? := some table
    let rootType := (vertex raw raw.root).type
    let baseIds := armSeeds raw false
    let baseTypes := baseIds.map (vertex raw · |>.type)
    if (← IO.getEnv "SEARCH_REDUCTION_NOMINATORS") == some "core" then
      discard <| boundedRebuildBranch do
        let nominations ← coreCertificateNominations rootType baseTypes
        certificateNominations.modify (· ++ nominations)
        return {detail := "core-nominations;not-negative-evidence"}
    let mut vertices := []
    for v in raw.vertices do
      let mut v := v
      if v.structureSeed then
        let part ← analyticPremise v.type rootType
        let inverse ← analyticPremise rootType v.type
        v := {v with targetPart := part || inverse}
      vertices := vertices ++ [v]
    raw := {raw with vertices}
    let graph ← annotateGraph {raw with edges := raw.edges ++ k2Frontier raw}
    lookupPhase "graph/certificates-start"
    let graph ← priceGraph graph false false lookup?
    let graph ← priceGraph graph true false lookup?
    let graph ← if (← IO.getEnv "SEARCH_REDUCTION_GIVEN_ABLATION") == some "1" then
        priceGraph graph false true lookup? >>= fun graph => priceGraph graph true true lookup?
      else pure {graph with edges := graph.edges.map fun edge => {edge with
        visibleCost := if edge.cost == .zero then .zero else .unknown,
        pairedVisibleCost := if edge.pairedCost == .zero then .zero else .unknown,
        givenUsedPremises := edge.usedPremises, pairedGivenUsedPremises := edge.pairedUsedPremises}}
    let baseProbe ← rootProbe graph false lookup?
    let pairedProbe ← rootProbe graph true lookup?
    let graph := addRootProbe (addRootProbe graph baseProbe false) pairedProbe true
    lookupPhase "graph/lazy-start"
    let (graph, baseProbe, negativeCalls) ← refineBaseline graph lookup? baseProbe
    let mut graph := graph
    let mut independentCalls := 0
    let mut reverseCalls := 0
    let mut probed := []
    let exhaustive := (← IO.getEnv "SEARCH_REDUCTION_FULL_EVAL") == some "1"
    -- Excluding a seed may select another route. Recompute before every new
    -- probe, visiting each eligible seed at most once.
    for _ in [:graph.vertices.length] do
      if !exhaustive && !better (armInterval graph true).upper (armInterval graph).upper then break
      let selected := if exhaustive then armSeeds graph true else
        optimalSeeds (armGraph graph true false) costUpper (armSeeds graph true)
      let some id := selected.find? (fun id =>
          selectedStructureSeed graph selected id && !probed.contains id) | break
      probed := id :: probed
      let mut v := vertex graph id
      let independent ← localRebuild v.type baseTypes lookup? s!"target-part-independent:{id}"
      independentCalls := independentCalls + 1
      let toRun (result : LocalResult) := result.query.guardRun
      let independentRun := toRun independent
      v := {v with
        independentLookup := independentRun,
        independentLookupDetail := independent.detail}
      if independent.cost != .zero then
        let mut reverse ← certifyLocal v.type (rootType :: baseTypes) lookup? v.origin.constName?
        let decisive := positiveEligible && graph.complete && finite (armInterval graph).upper &&
          strictDrop (armInterval graph) (armInterval graph true) &&
          baseProbe.outcome == .exhausted
        if reverse.cost != .zero &&
            (exhaustive || needsReverseNegative decisive independentRun (toRun reverse)) then
          -- Reverse evidence affects only target-part exclusion, never prices.
          reverse ← localRebuild v.type (rootType :: baseTypes) lookup? s!"target-part-reverse:{id}"
          reverseCalls := reverseCalls + 1
        let reverseRun := toRun reverse
        v := {v with reverseLookup := reverseRun, reverseLookupDetail := reverse.detail}
        if targetPartDecision independentRun reverseRun == .found then
          v := {v with targetPart := true}
      graph := {graph with vertices := graph.vertices.map fun old =>
        if old.id == id then v else old}
      let edges := graph.edges.map fun edge =>
        if edge.pairedUsedPremises.any (fun p =>
            (vertex graph p).targetPart && !(vertex graph p).seed && !edge.analytic.contains p) then
          {edge with pairedCost := .unknown, pairedZeroProof := none, pairedCertificate? := none}
        else edge
      graph := {graph with edges}
    let baseSeeds := armSeeds graph false
    let pairSeeds := armSeeds graph true
    let k1 := {graph with edges := graph.edges.filter (·.window != 2)}
    let selectedSeeds := optimalSeeds (armGraph graph true false) costUpper pairSeeds
    let targetPartComplete := if better (armInterval graph true).upper (armInterval graph).upper
      then targetPartReady graph selectedSeeds else true
    let witnessEdges := graph.edges.zipIdx.filterMap fun (edge, i) =>
      if isWitnessEdge graph selectedSeeds edge then some i else none
    let reading : GraphReading := {
      graph, baseline := armInterval graph, paired := armInterval graph true,
      baselineK1 := armInterval k1, pairedK1 := armInterval k1 true,
      baselineVisible := armInterval graph false true, pairedVisible := armInterval graph true true,
      baselineProbe := baseProbe, pairedProbe, selectedSeeds, witnessEdges, targetPartComplete,
      noAuxiliary := !(raw.vertices.any (·.structureSeed)),
      selectedSeedDepths := selectedSeeds.map (fun id => (id, armInterval graph false false (some id))),
      proofHardSeeds := selectedSeeds.filter (fun id =>
        proofHardEligible graph selectedSeeds id
          (depth (armGraph graph false false true) costLower baseSeeds id)),
      pairedUsesSeed := selectedSeeds.any (selectedStructureSeed graph selectedSeeds),
      negativeCalls := negativeCalls + independentCalls + reverseCalls,
      reverseNegativeCalls := reverseCalls,
      certificatePool := ← certificateNominations.get,
      certificateBindings := bindings,
      lookupEnabled := table.enabled, lookupBasisComplete := table.complete,
      queryRecords := ← currentQueryRecords.get,
      queryAnswerMemoization := ← localMemoEnabled}
    lookupPhase s!"graph/lazy-end negative_calls={reading.negativeCalls}"
    return reading
  finally
    certificateNominations.set previousPool
    edgeCertificateNominations.set previousBindings
    localMemoContext.set ""
    localMemoAnswers.set {}
    certificateOnlyAnswers.set {}

/-- A1 changes only the price mapping of this run's records. It performs no
search, restores no old cache, and preserves every guard completion state. -/
def priceMappingV18 (r : GraphReading) : GraphReading := Id.run do
  let graph := {r.graph with edges := r.graph.edges.map fun e => {e with
    cost := if e.query.budget then .unknown else e.cost,
    pairedCost := if e.pairedQuery.budget then .unknown else e.pairedCost}}
  let selectedSeeds := optimalSeeds (armGraph graph true false) costUpper (armSeeds graph true)
  return {r with
    graph,
    baseline := {armInterval graph with upper := r.baseline.upper},
    paired := {armInterval graph true with upper := r.paired.upper},
    selectedSeeds,
    witnessEdges := graph.edges.zipIdx.filterMap fun (e, i) =>
      if isWitnessEdge graph selectedSeeds e then some i else none,
    baselineProbe := if r.baselineProbe.query.budget then
      {r.baselineProbe with outcome := .incomplete .undecided} else r.baselineProbe}

end LeanInformationAudit.SearchReduction
