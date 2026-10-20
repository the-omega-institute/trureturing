import Mathlib.Tactic.Hint
import Lean.Meta.LazyDiscrTree

/-! Query-local structural retrieval. Only matching entries survive a scan;
no full-environment enumeration or index is retained by the production runner. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta

/-- Optional phase telemetry has no role in search or classification. -/
def profilePhase (label : String) : IO Unit := do
  if let some path ← IO.getEnv "SEARCH_REDUCTION_PROFILE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn s!"{← IO.monoMsNow} {label}"

abbrev Fact := Name × List Name

private def allowed (name : Name) (info : ConstantInfo) : Bool :=
  !info.isUnsafe && !(name.isInternalDetail && !isPrivateName name)

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

/-- A coarse retrieval key keeps definitionally equal full statements in reach
when their nested compiler-generated matchers have different constant names.
The key is never evidence of equality: each hit still requires `isDefEq`. -/
private def expressionHead (e : Expr) : Name :=
  e.consumeMData.getAppFn.constName?.getD .anonymous

partial def statementHead : Expr → List Name
  | .forallE _ domain body _ => expressionHead domain :: statementHead body
  | .mdata _ body => statementHead body
  | e => [expressionHead e]

/-- Only compiler matcher names may differ in this full-statement fallback.
The marker is a retrieval key, never a term submitted to the kernel. -/
def matcherShape (type : Expr) : Expr :=
  type.replace fun expression =>
    match expression with
    | .const (.str _ part) levels =>
      if part.startsWith "match_" then
        some (.const `_searchReduction.matcherShape levels)
      else none
    | _ => none

/-- A cheap syntactic prefilter avoids normalizing arbitrary mathematical
predicates merely to discover that they contain no logical pair. -/
private partial def pairHead (env : Environment) (expression : Expr)
    (seen : NameSet := {}) : Bool :=
  match expression with
  | .lam _ _ body _ | .forallE _ _ body _ | .mdata _ body => pairHead env body seen
  | .letE _ _ value body _ => pairHead env (body.instantiate1 value) seen
  | expression =>
    match expression.getAppFn with
    | .const name _ =>
      if name == ``And || name == ``Iff then true
      else if seen.contains name then false
      else match env.find? name with
        | some (.defnInfo value) => pairHead env value.value (seen.insert name)
        | _ => false
    | _ => false


/-- The reference implementation is exercised only by the explicit equivalence
suite. Its entries and enumeration order are the original eager algorithm. -/
structure ReferenceIndex where
  statements : Std.HashMap UInt64 (Array Name) := {}
  statementHeads : Std.HashMap (List Name) (Array Name) := {}
  projections : LazyDiscrTree Fact := {}

/-- Production state is constant size. The optional query-record handle belongs
to an explicitly requested test, never the ordinary compiled-audit path. -/
structure FactIndex where
  environment? : Option Environment := none
  localContext : LocalContext := {}
  localInstances : LocalInstances := #[]
  enumerationSize : Nat := 0
  verificationGroup? : Option Nat := none

/-- Keep a declaration's temporary normalization caches out of the next one.
Fresh-name allocation is preserved because retained entries own local contexts. -/
private def scratch (action : MetaM α) : MetaM α := do
  let initial ← get
  let cache := (← getThe Core.State).cache
  try action finally
    set initial
    modifyThe Core.State fun state => {state with cache}

private def referenceIndex : MetaM ReferenceIndex := do
  let env ← getEnv
  let names := env.constants.toList.toArray.qsort (fun a b => Name.quickLt a.1 b.1)
  let mut index : LazyDiscrTree.PreDiscrTree Fact := {}
  let mut statements : Std.HashMap UInt64 (Array Name) := {}
  let mut statementHeads : Std.HashMap (List Name) (Array Name) := {}
  for (name, info) in names do
    unless allowed name info do continue
    let key := info.type.hash
    statements := statements.insert key ((statements[key]?.getD #[]).push name)
    let head := statementHead info.type
    unless (head.getLast!).isAnonymous do
      statementHeads := statementHeads.insert head ((statementHeads[head]?.getD #[]).push name)
    unless pairHead env (telescopeBody info.type) do continue
    index ← scratch <| forallTelescopeReducing info.type fun _ body => do
      let body ← whnf body
      if body.isAppOfArity ``And 2 || body.isAppOfArity ``Iff 2 then
        indexType index name [] body
      else pure index
  return {statements, statementHeads, projections := index.toLazy}

private inductive VerificationQuery where
  | statement (key : UInt64) (actual : Array Name)
  | matcher (key : List Name) (actual : Array Name)
  | projection (query : Expr) (actual : Array Fact) (environment : Environment)
      (context : Meta.Context) (state : Meta.State)

private structure VerificationGroup where
  environment : Environment
  context : Meta.Context
  state : Meta.State
  queries : Array VerificationQuery := #[]

/-- Test records are scoped to one outer probe, including its negative replay.
Production queries allocate no records and retain no previous target. -/
private initialize verificationGroups : IO.Ref (Array VerificationGroup) ← IO.mkRef #[]

def resetIndexVerification : IO Unit := verificationGroups.set #[]

def factIndex : MetaM FactIndex := do
  let env ← getEnv
  let enumerationSize := env.constants.fold (fun n _ _ => n + 1) 0
  let verify := (← IO.getEnv "SEARCH_REDUCTION_VERIFY_INDEX") == some "1"
  let localContext ← getLCtx
  let localInstances ← getLocalInstances
  let verificationGroup? ← if verify then do
    let groups ← verificationGroups.get
    verificationGroups.set (groups.push {
      environment := env, context := ← read, state := ← get})
    pure (some groups.size)
  else pure none
  return {
    environment? := some env, localContext, localInstances, enumerationSize, verificationGroup?}

private def recordQuery (index : FactIndex) (query : VerificationQuery) : IO Unit := do
  if let some group := index.verificationGroup? then
    verificationGroups.modify fun groups => groups.modify group fun entry =>
      {entry with queries := entry.queries.push query}

private def checkCandidates [BEq α] (kind : String) (actual expected : Array α) :
    MetaM Unit := do
  unless actual == expected do
    IO.eprintln s!"search.index_equivalence_failed: {kind}, new={actual.size}, old={expected.size}"
    IO.Process.exit 1
  IO.eprintln s!"index-equivalence kind={kind} equal=true candidates={actual.size}"

/-- Replay the original eager index after the production search has completed.
Its independent, unbounded test context cannot spend any R_v1 search budget.
Every lookup, including lookups whose StateRefT state is discarded, is recorded.
The records are detached before replay and released at the end of this probe. -/
def verifyIndexQueries : IO Unit := do
  let groups ← verificationGroups.swap #[]
  for group in groups do
    if group.queries.isEmpty then continue
    let work : CoreM Unit := do
      let mut reference ← referenceIndex.run' group.context group.state
      for query in group.queries do
        match query with
        | .statement key actual =>
          (checkCandidates "statement" actual (reference.statements[key]?.getD #[])).run'
        | .matcher key actual =>
          (checkCandidates "matcher" actual (reference.statementHeads[key]?.getD #[])).run'
        | .projection query actual env context state =>
          let (expected, warmed) ← (withEnv env <| reference.projections.getMatch query).run' context state
          reference := {reference with projections := warmed}
          (checkCandidates "projection" actual (expected.appendResults #[])).run'
    let context : Core.Context := {
      fileName := "<index equivalence>", fileMap := default,
      options := (({} : Options).set `maxHeartbeats 0).set `maxRecDepth 1000,
      initHeartbeats := ← IO.getNumHeartbeats, maxHeartbeats := 0}
    match ← (work.run context {env := group.environment}).toIO' with
    | .ok (_, state) =>
      if state.messages.hasErrors then
        IO.eprintln "search.index_equivalence_oracle_errors"
        IO.Process.exit 1
    | .error ex =>
      IO.eprintln s!"search.index_equivalence_oracle_failed: {← ex.toMessageData.toString}"
      IO.Process.exit 1

/-- Hash collisions remain candidates; equality is still checked by the caller. -/
def statementCandidates (key : UInt64) : StateRefT FactIndex MetaM (Array Name) := do
  let some env := (← get).environment? | return #[]
  let names := env.constants.fold (init := #[]) fun names name info =>
    if allowed name info && info.type.hash == key then names.push name else names
  let names := names.qsort Name.quickLt
  if (← get).verificationGroup?.isSome then
    recordQuery (← get) (.statement key names)
  return names

/-- Preserve the old coarse bucket, including candidates rejected by the
subsequent matcher-shape and kernel equality checks. -/
def matcherCandidates (key : List Name) : StateRefT FactIndex MetaM (Array Name) := do
  let some env := (← get).environment? | return #[]
  let names := env.constants.fold (init := #[]) fun names name info =>
    if allowed name info && statementHead info.type == key && !key.getLast!.isAnonymous
      then names.push name else names
  let names := names.qsort Name.quickLt
  if (← get).verificationGroup?.isSome then
    recordQuery (← get) (.matcher key names)
  return names

/-- A singleton lookup uses Lean's exact wildcard, arrow and scoring semantics.
Removing an entry with no match changes no visited value or candidate order. -/
private def matchingEntries (index : FactIndex) (env : Environment)
    (query : Expr) (name : Name) (info : ConstantInfo) :
    MetaM (Array (LazyDiscrTree.InitEntry Fact)) := scratch do
  let tree ← withEnv env <| withLCtx index.localContext index.localInstances <|
      forallTelescopeReducing info.type fun _ body => do
    let body ← whnf body
    if body.isAppOfArity ``And 2 || body.isAppOfArity ``Iff 2 then
      indexType {} name [] body
    else pure {}
  let mut entries := #[]
  for (key, slot) in tree.roots.toArray do
    for entry in tree.tries[slot]! do
      let singleton := ({} : LazyDiscrTree.PreDiscrTree Fact).push key entry
      let (hits, _) ← singleton.toLazy.getMatch query
      unless hits.size == 0 do entries := entries.push {key, entry}
  return entries

/-- Scan with one declaration's scratch space. Retain only exact matching
entries, then restore original name/insertion order before the same tree query.
The live allocation is bounded by the query, its hits and the largest single
statement expansion, rather than an array or tree over all constants. -/
def projectionCandidates (query : Expr) : StateRefT FactIndex MetaM (Array Fact) := do
  let some env := (← get).environment? | return #[]
  let index ← get
  let entries ← env.constants.foldM (init := #[]) fun entries name info => do
    if !allowed name info || !pairHead env (telescopeBody info.type) then return entries
    let matchedEntries ← matchingEntries index env query name info
    return if matchedEntries.isEmpty then entries else entries.push (name, matchedEntries)
  let entries := entries.qsort (fun a b => Name.quickLt a.1 b.1)
  let mut tree : LazyDiscrTree.PreDiscrTree Fact := {}
  let mut retained := 0
  for (_, matchedEntries) in entries do
    for entry in matchedEntries do
      tree := tree.push entry.key entry.entry
      retained := retained + 1
  let (hits, _) ← tree.toLazy.getMatch query
  let actual := hits.appendResults #[]
  IO.eprintln s!"structural query: retained_entries={retained}, candidates={actual.size}"
  if index.verificationGroup?.isSome then
    recordQuery index (.projection query actual (← getEnv) (← read) (← getThe Meta.State))
  return actual

end LeanInformationAudit.SearchReduction
