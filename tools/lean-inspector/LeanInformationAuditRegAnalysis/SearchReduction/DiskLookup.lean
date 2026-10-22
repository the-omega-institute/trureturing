import Lean
import Batteries.Util.Pickle
import Lean.Meta.DiscrTree
import Lean.Meta.Tactic.LibrarySearch

/-! Module-owned, versioned discrimination trees stored in compacted regions.
Only candidate certificates carry semantic authority. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta

/-- Independent per-branch preparation allocation, in user-facing heartbeats. -/
abbrev lookupPreparationBudget : Nat := 2000000

structure LookupBudgetState where
  preparation : Nat := 0
  preparationNs : Nat := 0
  deriving Inhabited

/-- Only immutable I/O and deterministic byte transport belong here. Semantic
normalization, matching, synthesis and kernel checks keep the search clock.
Lean's thread-local heartbeat counter is restored after charging preparation. -/
def withLookupPreparation {α : Type} (budget? : Option (IO.Ref LookupBudgetState))
    (action : MetaM α) : MetaM α := do
  let some budget := budget? | return ← action
  let before ← budget.get
  if before.preparation >= lookupPreparationBudget * 1000 then
    Core.throwMaxHeartbeat `lookup.preparation `maxHeartbeats (lookupPreparationBudget * 1000)
  let started ← IO.getNumHeartbeats
  let nanos ← IO.monoNanosNow
  try
    withTheReader Core.Context (fun ctx => {ctx with
      initHeartbeats := started,
      maxHeartbeats := lookupPreparationBudget * 1000 - before.preparation}) do
      let result ← action
      checkSystem "lookup.preparation"
      return result
  finally
    let used := (← IO.getNumHeartbeats) - started
    let elapsed := (← IO.monoNanosNow) - nanos
    budget.modify fun s => {s with
      preparation := s.preparation + used, preparationNs := s.preparationNs + elapsed}
    IO.setNumHeartbeats started

namespace DiskLookup

abbrev version : String := "R_lookup/discrtree-pickle-v5"

structure Entry where
  module : String
  name : String
  parts : Array (String × Nat)
  ordinal : Nat := 0
  /-- Dropped-key provenance; never used for matching or certification. -/
  route : String := ""
  deriving ToJson, FromJson, Inhabited, BEq

def Entry.leanName (entry : Entry) : Name :=
  entry.parts.foldl (fun parent (text, number) =>
    if number == 0 then .str parent text else .num parent (number - 1)) .anonymous

private def nameParts : Name → Array (String × Nat)
  | .anonymous => #[]
  | .str parent text => (nameParts parent).push (String.ofList text.toList, 0)
  | .num parent n => (nameParts parent).push ("", n + 1)

structure Header where
  format : String := version
  basis : String
  mathlib : String
  inputs : UInt64
  storage : String
  root : String
  digest : UInt64
  complete : Bool
  modules : Nat
  declarations : Nat
  indexed : Nat
  missing : Array String
  deriving ToJson, FromJson, Inhabited

private def runGit (args : Array String) : IO String := do
  let result ← IO.Process.output {cmd := "git", args}
  unless result.exitCode == 0 do throw <| IO.userError result.stderr
  return result.stdout.trimAscii.toString

/-- Read compiler module data without importing a full environment. All module
parts, including private declarations, participate in the coverage counts. -/
private unsafe def moduleParts (name : Name) : IO (Array (ModuleData × CompactedRegion)) := do
  let file ← findOLean name
  let main ← readModuleData file
  if !main.1.isModule then return #[main]
  let parts ← readModuleDataParts #[file, OLeanLevel.server.adjustFileName file,
    OLeanLevel.private.adjustFileName file]
  main.2.free
  return parts

private def ownedName : Name → Name
  | .anonymous => .anonymous
  | .str parent text => .str (ownedName parent) (String.ofList text.toList)
  | .num parent n => .num (ownedName parent) n
private def ownedString (s : String) : String := String.ofList s.toList

/-- The callback retains only freshly allocated metadata. The module payload
has left scope before its regions are released in reverse dependency order. -/
@[noinline] private unsafe def visitModule (name : Name)
    (visit : Array ModuleData → IO α) : IO α := do
  let (result, regions) ← do
    let parts ← moduleParts name
    let result ← visit (parts.map (·.1))
    pure (result, parts.map (·.2))
  for region in regions.reverse do region.free
  return result


structure Manifest where
  roots : Array (UInt64 × Array String) := #[]
  deriving ToJson, FromJson, Inhabited

def statementPrimitive (n : Name) : Bool :=
  #[``And, ``Iff, ``True, ``False, ``Eq, ``Nat, ``Int,
    ``HAdd.hAdd, ``HMul.hMul, ``HSub.hSub, ``Neg.neg, ``OfNat.ofNat,
    ``LE.le, ``LT.lt, ``Nat.add, ``Nat.mul, ``Nat.sub, ``Int.add,
    ``Int.mul, ``Int.sub, ``Int.neg].contains n


partial def statementAliasBody (env : Environment) (e : Expr) : Bool :=
  match e with
  | .lam _ _ b _ => statementAliasBody env b
  | .forallE _ d b _ => statementAliasBody env d && statementAliasBody env b
  | .app f a => statementAliasBody env f && statementAliasBody env a
  | .const n _ => !(match (env.setExporting false).find? n with
      | some (.ctorInfo _) => !statementPrimitive n | _ => false) &&
    !((n.toString.splitOn "match_").length > 1 || n.toString.endsWith ".rec" ||
      n.toString.endsWith ".recOn" || n.toString.endsWith ".brecOn" ||
      n.toString.endsWith ".below" || n.toString.endsWith ".ibelow" ||
      n.toString.endsWith ".casesOn")
  | .bvar _ | .sort _ | .lit _ => true
  | .mdata _ b => statementAliasBody env b
  | _ => false


partial def statementInstanceParameters : Expr → Bool
  | .forallE _ _ body kind => kind == .instImplicit || statementInstanceParameters body
  | _ => false


abbrev membershipNormalizationFuel : Nat := 2000000

structure StatementNormalizationState where
  remaining : Nat
  memo : Std.HashMap (Expr × List Name) Expr := {}

/-- Memoization includes the alias stack; it changes work, never N's result. -/
partial def normalizeStatementAux (env : Environment) (e : Expr)
    (seen : List Name) : StateT StatementNormalizationState (Except String) Expr := do
  if let some result := (← get).memo[(e, seen)]? then return result
  let remaining := (← get).remaining
  if remaining == 0 then throw "search.presentation_normalization_fuel"
  modify fun state => {state with remaining := remaining - 1}
  let compute : Unit → StateT StatementNormalizationState (Except String) Expr := fun _ => do
    let e := e.consumeMData
    match e with
    | .app .. | .const .. =>
      let fn := e.getAppFn
      -- Instance dictionaries implement general computation. Keep their entire
      -- subtrees opaque, including when they are arguments of arithmetic syntax.
      let mut parameterType : Option Expr := match fn with
        | .const n _ => ((env.setExporting false).find? n).map (·.type)
        | _ => none
      let mut args : Array Expr := #[]
      for arg in e.getAppArgs do
        let instanceArg : Bool := match parameterType with
          | some (.forallE _ _ _ kind) => kind == .instImplicit
          | _ => false
        let normalized ← if instanceArg then pure arg else normalizeStatementAux env arg seen
        args := args.push normalized
        parameterType := match parameterType with
          | some (.forallE _ _ body _) => some body
          | _ => none
      if let .const n us := fn then
        if seen.contains n then throw "search.presentation_alias_cycle"
        if !statementPrimitive n then
          if let some (.defnInfo d) := (env.setExporting false).find? n then
            if !statementInstanceParameters d.type && statementAliasBody env d.value then
              let body := d.value.instantiateLevelParams d.levelParams us
              return ← normalizeStatementAux env (body.beta args) (n :: seen)
      return mkAppN fn args
    | .forallE n d b bi =>
      return .forallE n (← normalizeStatementAux env d seen)
        (← normalizeStatementAux env b seen) bi
    | .lam n d b bi =>
      return .lam n (← normalizeStatementAux env d seen)
        (← normalizeStatementAux env b seen) bi
    | _ => return e
  let result ← compute ()
  modify fun state => {state with memo := state.memo.insert (e, seen) result}
  return result

def normalizeStatementSyntax (env : Environment) (e : Expr)
    (fuel : Nat := membershipNormalizationFuel) : Except String Expr :=
  (normalizeStatementAux env e []).run' {remaining := fuel}

abbrev membershipVersion : String := "R_lookup/membership-alpha-syntax-v3-memo-2000000"

structure MembershipHeader where
  format : String := membershipVersion
  inputs : UInt64
  storage : String
  complete : Bool
  indexed : Nat
  missing : Array String := #[]
  deriving ToJson, FromJson

abbrev MembershipPage := Std.HashMap UInt64 (Array Entry)

private partial def alphaExpression (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
  if let some result := (← get)[e]? then return result
  let result ← match e with
    | .app f a => do
      let f ← alphaExpression f
      let a ← alphaExpression a
      if f.isLambda then alphaExpression (f.beta #[a]) else pure (.app f a)
    | .lam _ t b _ => return .lam `_ (← alphaExpression t) (← alphaExpression b) .default
    | .forallE _ t b _ => return .forallE `_ (← alphaExpression t) (← alphaExpression b) .default
    | .letE _ _ v b _ => alphaExpression (b.instantiate1 v)
    | .mdata _ b => alphaExpression b
    | .proj n i b => return .proj n i (← alphaExpression b)
    | e => pure e
  modify (·.insert e result)
  return result

/-- Full statements use the shared frozen syntax normalization. Recursive
computations and instance dictionaries remain opaque. De Bruijn binders and
canonical universe parameters supply the alpha quotient. -/
def membershipKey (type : Expr) : MetaM UInt64 := do
  let type ← instantiateMVars type
  let type := (alphaExpression type).run' {}
  let type ← match normalizeStatementSyntax (← getEnv) type with
    | .ok type => pure type
    | .error reason => throwError "{reason}"
  let params := (collectLevelParams {} type).params.toList
  let levels := (List.range params.length).map fun i => Level.param (.num `membership i)
  let type := type.instantiateLevelParams params levels
  return ((alphaExpression type).run' {}).hash

structure Index where
  directory : System.FilePath
  header : Header
  excluded : Array Name := #[]
  manifest : Array (UInt64 × Array String) := #[]
  membership? : Option MembershipHeader := none

structure Candidates where
  entries : Array Entry := #[]
  missing : Array String := #[]
  complete : Bool := false
  pages : Nat := 0
  deriving Inhabited

private def readJson [FromJson α] (path : System.FilePath) : IO α := do
  IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse (← IO.FS.readFile path))

private def writeJson [ToJson α] (path : System.FilePath) (value : α) : IO Unit := do
  IO.FS.writeFile (path.addExtension "tmp") (toJson value).compress
  IO.FS.rename (path.addExtension "tmp") path

structure Collision where
  constant : String
  modules : Array String
  deriving ToJson, FromJson

structure ModuleSummary where
  name : String
  declarations : Nat
  indexed : Nat := 0
  deriving ToJson, FromJson

structure ShardPlan where
  modules : Array String
  deriving ToJson, FromJson

structure ShardResult where
  routes : Array (UInt64 × Array String) := #[]
  coverage : Array ModuleSummary := #[]
  missing : Array String := #[]
  deriving ToJson, FromJson

structure PickledShard where
  tree : DiscrTree Entry := {}
  fallback : Array Entry := #[]

private def rootKey (key : DiscrTree.Key) : UInt64 := hash key

private def dropped (keys : Array DiscrTree.Key) : Bool :=
  keys == #[.star] || keys == #[.const ``Eq 3, .star, .star, .star]

private def copyEntry (e : Entry) : Entry := {
  module := String.ofList e.module.toList, name := String.ofList e.name.toList,
  parts := e.parts.map fun (s, n) => (String.ofList s.toList, n),
  ordinal := e.ordinal, route := String.ofList e.route.toList}

private unsafe def importEnvironment (roots : Array Name) : IO Environment := do
  enableInitializersExecution
  withImporting do
    let imports := roots.map fun module => {module : Import}
    let (_, state) ← (importModulesCore imports).run default
    finalizeImport state imports {} 0 (leakEnv := false) (loadExts := true)

/-- Telescope variables become metavariables before the core path builder is
called. Projections and direction conversions use their actual Lean types. -/
private partial def viewPaths (type : Expr) (fuel : Nat := 32) : MetaM (Array (Array DiscrTree.Key)) := do
  if fuel == 0 then return #[← DiscrTree.mkPath (← mkFreshExprMVar (mkSort .zero))]
  let (_, _, body) ← forallMetaTelescopeReducing type
  let body ← withReducible <| whnf body
  let mut paths := #[← DiscrTree.mkPath body]
  if body.isAppOfArity ``And 2 then
    for i in [:2] do paths := paths ++ (← viewPaths (body.getArg! i) (fuel - 1))
  if body.isAppOfArity ``Iff 2 then
    paths := paths ++ (← viewPaths (← mkArrow (body.getArg! 0) (body.getArg! 1)) (fuel - 1))
    paths := paths ++ (← viewPaths (← mkArrow (body.getArg! 1) (body.getArg! 0)) (fuel - 1))
  if body.isAppOfArity ``Eq 3 then
    paths := paths.push (← DiscrTree.mkPath (mkAppN body.getAppFn
      #[body.getArg! 0, body.getArg! 2, body.getArg! 1]))
    if body.getArg! 0 == mkSort .zero then
      paths := paths ++ (← viewPaths (← mkArrow (body.getArg! 1) (body.getArg! 2)) (fuel - 1))
      paths := paths ++ (← viewPaths (← mkArrow (body.getArg! 2) (body.getArg! 1)) (fuel - 1))
  if body.isAppOfArity ``Subtype 2 then
    let witness ← mkFreshExprMVar (body.getArg! 0)
    paths := paths ++ (← viewPaths ((body.getArg! 1).beta #[witness]) (fuel - 1))
  return paths

private unsafe def pathsInEnvironment (env : Environment) (type : Expr)
    (label : String) : IO (Array (Array DiscrTree.Key)) := do
  let work : CoreM (Array (Array DiscrTree.Key)) := MetaM.run' do
    tryCatchRuntimeEx (viewPaths type) fun ex => do
      if ex.isInterrupt || ex.isMaxHeartbeat then throw ex
      IO.eprintln s!"lookup.path_fallback declaration={label} reason={← ex.toMessageData.toString}"
      return #[← DiscrTree.mkPath (← mkFreshExprMVar (mkSort .zero))]
  let context : Core.Context := {
    fileName := "<lookup-index>", fileMap := default,
    options := (({} : Options).set `maxHeartbeats 0).set `maxRecDepth 1000,
    initHeartbeats := ← IO.getNumHeartbeats, maxHeartbeats := 0}
  match ← (work.run context {env}).toIO' with
  | .ok (value, state) =>
    if state.messages.hasErrors then throw <| IO.userError "lookup.discrtree_path_errors"
    return value
  | .error ex => throw <| IO.userError s!"lookup.discrtree_path_failed:{← ex.toMessageData.toString}"

/-- A child owns one import closure and writes only its assigned modules.
Its exit releases the whole Environment before the next shard starts. -/
unsafe def produceShard (storage : System.FilePath) (planPath resultPath : System.FilePath) : IO Unit := do
  let plan : ShardPlan ← readJson planPath
  let env ← importEnvironment (plan.modules.map String.toName)
  let mut result : ShardResult := {}
  let mut payload : PickledShard := {}
  let mut roots : Std.HashSet UInt64 := {}
  let mut batchModules : Array String := #[]
  for module in plan.modules do
    let (nextPayload, nextRoots, summary) ← visitModule module.toName fun parts => do
      let mut payload := payload
      let mut roots := roots
      let mut count := 0
      let mut indexed := 0
      let mut known : NameSet := {}
      for part in parts do
        for info in part.constants do
          if known.contains info.name then continue
          known := known.insert info.name
          count := count + 1
          let some stable := (env.setExporting false).find? info.name
            | throw <| IO.userError s!"lookup.declaration_not_loaded:{info.name}"
          if stable.isUnsafe || LazyDiscrTree.blacklistInsertion env info.name ||
              Linter.isDeprecated env info.name || info.name.isMetaprogramming then continue
          let entry : Entry := {
            module, name := ownedString info.name.toString,
            parts := nameParts info.name, ordinal := count}
          let paths ← pathsInEnvironment env stable.type s!"{module}:{info.name}"
          let mut seen : Std.HashSet (Array DiscrTree.Key) := {}
          for keys in paths do
            if seen.contains keys then continue
            seen := seen.insert keys
            let fallback := dropped keys
            let entry := if fallback then
                {entry with route := if keys == #[.star] then "star" else "eq-star"}
              else entry
            let bucket := if fallback then rootKey .star else rootKey (keys[0]?.getD .star)
            roots := roots.insert bucket
            payload := if fallback then {payload with fallback := payload.fallback.push entry}
              else {payload with tree := payload.tree.insertKeyValue keys entry}
          indexed := indexed + 1
      return (payload, roots, ({name := module, declarations := count, indexed} : ModuleSummary))
    payload := nextPayload
    roots := nextRoots
    result := {result with coverage := result.coverage.push summary}
    batchModules := batchModules.push module
    if batchModules.size == 128 || result.coverage.size == plan.modules.size then
      let file := s!"batch-{hash batchModules}.pickle"
      pickle (storage / file) payload (key := .str `lookup file)
      let routes := roots.toArray.map fun bucket => (bucket, #[file])
      result := {result with routes := result.routes ++ routes}
      payload := {}
      roots := {}
      batchModules := #[]
    if result.coverage.size % 256 == 0 then
      IO.FS.writeFile (resultPath.addExtension "progress") s!"{result.coverage.size}/{plan.modules.size}"

  writeJson resultPath result

private unsafe def runShard (storage : System.FilePath) (modules : Array String)
    (label : String) : IO ShardResult := do
  let plan := storage / s!"plan-{label}.json"
  let result := storage / s!"result-{label}.json"
  try
    let old : ShardResult ← readJson result
    if old.missing.isEmpty && (old.coverage.map (·.name)).qsort (· < ·) == modules.qsort (· < ·) then
      IO.eprintln s!"lookup.import_shard={label} modules={modules.size} status=reused"
      return old
  catch _ => pure ()
  writeJson plan ({modules} : ShardPlan)
  let app ← IO.appPath
  let output ← IO.Process.output {
    cmd := app.toString,
    args := #["--shard", storage.toString, plan.toString, result.toString]}
  unless output.stderr.isEmpty do IO.eprint output.stderr
  if output.exitCode == 0 then
    IO.eprintln s!"lookup.import_shard={label} modules={modules.size} status=complete"
    return ← readJson result
  IO.eprintln s!"lookup.import_shard={label} modules={modules.size} status=failed {output.stderr}"
  if modules.size <= 1 then return {missing := modules.map fun name => s!"{name}: {output.stderr}"}
  let half := modules.size / 2
  let a ← runShard storage (modules.extract 0 half) (label ++ "a")
  let b ← runShard storage (modules.extract half modules.size) (label ++ "b")
  return {
    routes := a.routes ++ b.routes
    coverage := a.coverage ++ b.coverage
    missing := a.missing ++ b.missing}

private abbrev Signature := Std.HashMap Name Name

private unsafe def signature (graph : Std.HashMap Name (Array Name))
    (own : Std.HashMap Name (Array Name)) (module : Name) :
    StateM (Std.HashMap Name (Signature × Bool)) (Signature × Bool) := do
  if let some cached := (← get)[module]? then return cached
  let mut result : Signature := {}
  let mut valid := true
  for dep in graph[module]?.getD #[] do
    unless dep.toString.startsWith "D5." do continue
    let (inherited, clean) ← signature graph own dep
    valid := valid && clean
    for (constant, owner) in inherited.toArray do
      if let some previous := result[constant]? then
        if previous != owner then valid := false
      result := result.insert constant owner
  for constant in own[module]?.getD #[] do
    if let some previous := result[constant]? then
      if previous != module then valid := false
    result := result.insert constant module
  modify (·.insert module (result, valid))
  return (result, valid)

private def compatible (a b : Signature) : Bool :=
  b.toArray.all fun (constant, owner) => (a[constant]?).all (· == owner)

private unsafe def partitionImports (modules : Array Name)
    (graph : Std.HashMap Name (Array Name)) (collisions : Array Collision) : Array (Array Name) := Id.run do
  let mut own : Std.HashMap Name (Array Name) := {}
  for collision in collisions do
    for owner in collision.modules do
      own := own.insert owner.toName ((own[owner.toName]?.getD #[]).push collision.constant.toName)
  let mut cache := {}
  let mut assignments := #[]
  for module in modules do
    let (result, next) := (signature graph own module).run cache
    cache := next
    assignments := assignments.push (module, result)
  assignments := assignments.qsort fun a b => a.2.1.size > b.2.1.size
  let mut groups : Array (Array Name × Signature) := #[]
  for (module, sig, _valid) in assignments do
    let mut placed := false
    for i in [:groups.size] do
      let (assigned, current) := groups[i]!
      if compatible current sig then
        let combined := sig.toArray.foldl (fun map (n, m) => map.insert n m) current
        groups := groups.set! i (assigned.push module, combined)
        placed := true
        break
    unless placed do groups := groups.push (#[module], sig)
  return groups.map (·.1)

/-- Fingerprints cover compiled data and explicit schema version. The producer
records duplicate definitions before attempting any combined import. -/
unsafe def produceMature (directory : System.FilePath) (basis mathlib : String)
    (roots : Array Name) (checkSources : Bool := true) : IO Header := do
  IO.FS.createDirAll directory
  if checkSources then
    discard <| runGit #["diff", "--quiet", basis, "--", "D5"]
    unless (← runGit #["-C", ".lake/packages/mathlib", "rev-parse", "HEAD"]) == mathlib do
      throw <| IO.userError "lookup.mathlib_snapshot_mismatch"
  let basisModules := roots.foldl (fun set n => set.insert n) ({} : NameSet)
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut modules : Array Name := #[]
  let mut missing : Array String := #[]
  let mut inputs : UInt64 := hash (version, basis, mathlib, Lean.versionString)
  let mut owners : Std.HashMap Name (Array String) := {}
  let mut graph : Std.HashMap Name (Array Name) := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    try
      let (deps, fingerprint, names) ← visitModule name fun parts => do
        let mut deps := #[]
        let mut fingerprint := 0
        let mut names := #[]
        for part in parts do
          for info in part.constants do
            fingerprint := mixHash fingerprint (mixHash info.type.hash (hash info.value?))
            if name.toString.startsWith "D5." then names := names.push (ownedName info.name)
          for dependency in part.imports do deps := deps.push (ownedName dependency.module)
        return (deps, fingerprint, names)
      graph := graph.insert name deps
      for n in names do
        let previous := owners[n]?.getD #[]
        unless previous.contains name.toString do owners := owners.insert n (previous.push name.toString)
      let olean ← findOLean name
      let mut fileFingerprint := hash (← IO.FS.readBinFile olean)
      for level in #[OLeanLevel.server, OLeanLevel.private] do
        let part := level.adjustFileName olean
        if ← part.pathExists then
          fileFingerprint := mixHash fileFingerprint (hash (← IO.FS.readBinFile part))
      inputs := mixHash inputs (mixHash (hash name) (mixHash fingerprint fileFingerprint))
      todo := todo ++ deps
      modules := modules.push name
      if modules.size % 1000 == 0 then IO.eprintln s!"lookup.inputs_summarized={modules.size}"
    catch ex => missing := missing.push s!"{name}: {ex}"
  let selected := (modules.qsort Name.quickLt).filter fun name =>
    !name.toString.startsWith "D5." || basisModules.contains name
  let collisions := owners.toArray.filterMap fun (n, ms) =>
    if ms.size > 1 then some ({constant := n.toString, modules := ms.qsort (· < ·)} : Collision) else none
  writeJson (directory / "import-collisions.json") (collisions.qsort fun a b => a.constant < b.constant)
  try
    let old : Header ← readJson (directory / "header.json")
    if old.format == version && old.basis == basis && old.mathlib == mathlib &&
        old.inputs == inputs && old.complete && old.modules == selected.size then
      let manifestText ← IO.FS.readFile (directory / old.storage / old.root)
      if hash manifestText == old.digest then
        IO.println (toJson old).compress
        return old
  catch _ => pure ()
  let storage := directory / s!"discrtree-pickle-v5-{inputs}"
  IO.FS.createDirAll storage
  let mut all : ShardResult := {missing}
  let ordinary := selected.filter fun n => !n.toString.startsWith "D5."
  let d5 := selected.filter fun n => n.toString.startsWith "D5."
  let groups := (#[ordinary]).filter (!·.isEmpty) ++ partitionImports d5 graph collisions
  IO.eprintln s!"lookup.import_partitions={groups.size} collision_constants={collisions.size}"
  writeJson (directory / "import-partitions.json") (groups.map fun group => group.map Name.toString)
  for chunk in [:groups.size] do
    let result ← runShard storage (groups[chunk]!.map Name.toString) s!"group-{chunk}"
    all := {
      routes := all.routes ++ result.routes, coverage := all.coverage ++ result.coverage,
      missing := all.missing ++ result.missing}
    writeJson (directory / "coverage.json") all
  let mut routes : Std.HashMap UInt64 (Array String) := {}
  for (bucket, files) in all.routes do routes := routes.insert bucket ((routes[bucket]?.getD #[]) ++ files)
  let manifest : Manifest := {roots := routes.toArray.map fun (root, files) => (root, files.qsort (· < ·))}
  writeJson (storage / "manifest.json") manifest
  let header : Header := {
    basis, mathlib, inputs, storage := storage.fileName.getD storage.toString,
    root := "manifest.json", digest := hash (toJson manifest).compress,
    complete := all.missing.isEmpty && all.coverage.size == selected.size,
    modules := selected.size, declarations := all.coverage.foldl (fun n m => n + m.declarations) 0,
    indexed := all.coverage.foldl (fun n m => n + m.indexed) 0, missing := all.missing}
  writeJson (directory / "header.json") header
  IO.println (toJson header).compress
  return header

structure MembershipShardResult where
  modules : Array String
  indexed : Nat := 0
  missing : Array String := #[]
  deriving ToJson, FromJson

private def membershipFile (bucket : Nat) : String := s!"members-{bucket}.pickle"

unsafe def produceMembershipShard (storage : System.FilePath)
    (planPath resultPath : System.FilePath) : IO Unit := do
  let plan : ShardPlan ← readJson planPath
  let progress := resultPath.addExtension "progress"
  IO.FS.writeFile progress "importing"
  let env ← importEnvironment (plan.modules.map String.toName)
  IO.FS.writeFile progress "imported"
  let mut pages : Std.HashMap Nat MembershipPage := {}
  let mut result : MembershipShardResult := {modules := plan.modules}
  for module in plan.modules do
    IO.FS.writeFile progress s!"normalizing:{module}"
    let entries ← visitModule module.toName fun parts => do
      let mut known : NameSet := {}
      let mut entries : Array Entry := #[]
      let mut ordinal := 0
      for part in parts do
        for info in part.constants do
          if known.contains info.name then continue
          known := known.insert info.name
          ordinal := ordinal + 1
          if info.isUnsafe || LazyDiscrTree.blacklistInsertion env info.name ||
              Linter.isDeprecated env info.name || info.name.isMetaprogramming then continue
          match info with
          | .thmInfo _ | .defnInfo _ | .opaqueInfo _ => pure ()
          | _ => continue
          entries := entries.push {
            module, name := ownedString info.name.toString,
            parts := nameParts info.name, ordinal}
      return entries
    for entry in entries do
      let work : CoreM UInt64 := MetaM.run' do
        membershipKey (← getConstInfo entry.leanName).type
      let context : Core.Context := {
        fileName := "<membership-index>", fileMap := default,
        options := (({} : Options).set `maxHeartbeats 0).set `maxRecDepth 1000,
        initHeartbeats := ← IO.getNumHeartbeats, maxHeartbeats := 0}
      match ← (work.run context {env}).toIO' with
      | .ok (key, state) =>
        if state.messages.hasErrors then
          result := {result with missing := result.missing.push s!"{module}:{entry.name}:normalization-errors"}
        else
          let bucket := key.toNat % 256
          let page := pages[bucket]?.getD {}
          pages := pages.insert bucket (page.insert key ((page[key]?.getD #[]).push entry))
          result := {result with indexed := result.indexed + 1}
      | .error ex =>
        result := {result with missing := result.missing.push s!"{module}:{entry.name}:{← ex.toMessageData.toString}"}
    if result.indexed % 10000 < entries.size then
      IO.eprintln s!"lookup.membership_indexed={result.indexed} module={module} missing={result.missing.size}"
  for bucket in [:256] do
    IO.FS.writeFile progress s!"writing:{bucket}"
    pickle (storage / membershipFile bucket) (pages[bucket]?.getD {})
      (key := .num `membership bucket)
  writeJson resultPath result
  IO.FS.writeFile progress "complete"

/-- Membership is an independently versioned sidecar. Existing discrimination
trees, fallback lists and their ordering are reused without regeneration. -/
unsafe def produceMembership (directory : System.FilePath) : IO MembershipHeader := do
  let header : Header ← readJson (directory / "header.json")
  unless header.format == version && header.complete do
    throw <| IO.userError "lookup.membership_requires_complete_candidate_index"
  let storage := directory / s!"membership-alpha-syntax-v3-memo-2000000-{header.inputs}"
  IO.FS.createDirAll storage
  let partitions : Array (Array String) ← readJson (directory / "import-partitions.json")
  let groups := partitions.mapIdx fun i modules => (s!"group-{i}", modules)
  let mut results : Array MembershipShardResult := #[]
  for i in [:groups.size] do
    let part := storage / groups[i]!.1
    IO.FS.createDirAll part
    let plan := part / "plan.json"
    let resultPath := part / "result.json"
    let cached ← try
      let old : MembershipShardResult ← readJson resultPath
      pure (if old.modules == groups[i]!.2 then some old else none)
      catch _ => pure none
    let result ← if let some old := cached then pure old else do
      writeJson plan ({modules := groups[i]!.2} : ShardPlan)
      let output ← IO.Process.output {
        cmd := (← IO.appPath).toString,
        args := #["--membership-shard", part.toString, plan.toString, resultPath.toString]}
      unless output.stderr.isEmpty do IO.eprint output.stderr
      unless output.exitCode == 0 do
        throw <| IO.userError s!"lookup.membership_shard_failed:{i}:{output.exitCode}"
      readJson resultPath
    results := results.push result
    IO.eprintln s!"lookup.membership_partition={i + 1}/{groups.size} indexed={result.indexed} missing={result.missing.size}"
  for bucket in [:256] do
    let mut page : MembershipPage := {}
    for i in [:groups.size] do
      let entries : Array (String × Array Entry) ← withUnpickle
        (storage / groups[i]!.1 / membershipFile bucket) fun (part : MembershipPage) =>
          pure (part.toArray.map fun (key, values) => (toString key, values.map copyEntry))
      for (text, values) in entries do
        let key := text.toNat!.toUInt64
        page := page.insert key ((page[key]?.getD #[]) ++ values)
    pickle (storage / membershipFile bucket) page (key := .num `membership bucket)
  let missing := results.foldl (fun all result => all ++ result.missing) #[]
  let result : MembershipHeader := {
    inputs := header.inputs,
    storage := storage.fileName.getD storage.toString,
    indexed := results.foldl (fun n result => n + result.indexed) 0,
    complete := missing.isEmpty, missing}
  writeJson (directory / "membership-header.json") result
  IO.println (toJson result).compress
  return result

/-- Compare the exact serialized key and identity of every previously completed
entry. Newly completed entries do not alter the old-result comparison. -/
unsafe def compareMembership (directory oldHeader : System.FilePath) : IO Bool := do
  let old : MembershipHeader ← readJson oldHeader
  let current : MembershipHeader ← readJson (directory / "membership-header.json")
  let mut previous : Std.HashMap (String × String) String := {}
  let mut now : Std.HashMap (String × String) String := {}
  for bucket in [:256] do
    for (header, isOld) in #[(old, true), (current, false)] do
      let rows ← withUnpickle (directory / header.storage / membershipFile bucket)
        fun (page : MembershipPage) => pure (page.toArray.foldl (fun rows (key, entries) =>
          rows ++ entries.map (fun entry =>
            ((ownedString entry.module, ownedString entry.name),
              (toJson (toString key, copyEntry entry)).compress))) #[])
      for (identity, bytes) in rows do
        if isOld then previous := previous.insert identity bytes
        else now := now.insert identity bytes
  let changed := previous.toArray.filter fun (identity, bytes) => now[identity]? != some bytes
  let equal := changed.isEmpty
  IO.println (Json.mkObj [
    ("completed_results_bytes_equal", toJson equal),
    ("old_completed", toJson previous.size), ("new_completed", toJson now.size),
    ("changed_or_lost", toJson changed.size),
    ("remaining_missing", toJson current.missing.size),
    ("comparison", toJson "UTF-8 JSON of membership key and full candidate metadata, per (module, Name)")]).compress
  return equal

def openIndex (directory : System.FilePath) (basis mathlib : String)
    (excluded : Array Name := #[]) : IO Index := do
  let header : Header ← readJson (directory / "header.json")
  let sameBasis ← if header.basis == basis then pure true else
    try pure ((← runGit #["rev-parse", header.basis]) == (← runGit #["rev-parse", basis]))
    catch _ => pure false
  unless header.format == version && sameBasis && header.mathlib == mathlib do
    throw <| IO.userError "lookup.index_snapshot_mismatch"
  let storage := directory / header.storage
  let text ← IO.FS.readFile (storage / header.root)
  unless hash text == header.digest do throw <| IO.userError "lookup.manifest_checksum"
  let manifest : Manifest ← IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse text)
  let membership? ← try
    let member : MembershipHeader ← readJson (directory / "membership-header.json")
    pure (if member.format == membershipVersion && member.inputs == header.inputs then some member else none)
    catch _ => pure none
  return {directory := storage, header, excluded, manifest := manifest.roots, membership?}

/-- One disk hash bucket, followed by an expected constant-time hash lookup.
No implication candidates or baseline declarations are enumerated here. -/
unsafe def queryMembership (index : Index) (type : Expr)
    (budget? : Option (IO.Ref LookupBudgetState) := none) : MetaM Candidates := do
  let some header := index.membership? | return {}
  let key ← membershipKey type
  let file := index.directory.parent.getD index.directory / header.storage /
    membershipFile (key.toNat % 256)
  try
    let entries ← withLookupPreparation budget? <| withUnpickle file fun (page : MembershipPage) =>
      pure ((page[key]?.getD #[]).map copyEntry)
    let entries := entries.filter fun entry => !index.excluded.contains entry.module.toName
    let entries := entries.qsort fun a b =>
      if a.module != b.module then a.module < b.module else a.ordinal < b.ordinal
    IO.eprintln s!"LOOKUP_COST backend=membership-alpha key={key} pages=1 candidates={entries.size}"
    return {entries, complete := header.complete && index.header.complete, pages := 1, missing := header.missing}
  catch ex =>
    if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
    IO.eprintln s!"lookup.membership_incomplete:{← ex.toMessageData.toString}"
    return {}

/-- The persisted core tree is queried while its mmap is alive. Only detached
candidate metadata leaves the callback. Fallback is requested after primary
certificate attempts fail; an incomplete pass cannot certify NoHit. -/
unsafe def queryMature (index : Index) (type : Expr)
    (heartbeatLimit? : Option Nat := none) (fallback : Bool := false)
    (budget? : Option (IO.Ref LookupBudgetState) := none) : MetaM Candidates := do
  let started ← IO.getNumHeartbeats
  let keys ← DiscrTree.mkPath type
  let bucket := if fallback then rootKey .star else rootKey (keys[0]?.getD .star)
  let mut entries : Array Entry := #[]
  let mut complete := index.header.complete
  let mut pages := 0
  let mut seen : Std.HashSet (String × Name) := {}
  let files := index.manifest.find? (fun item => item.1 == bucket) |>.map (·.2) |>.getD #[]
  for file in files do
    if let some limit := heartbeatLimit? then
      if (← IO.getNumHeartbeats) > limit then return {complete := false, pages}
    try
      let (shard, region) ← withLookupPreparation budget? <|
        (unpickle PickledShard (index.directory / file))
      let hits : Array Entry ← try
        let hits ← if fallback then pure shard.fallback else shard.tree.getMatch type
        withLookupPreparation budget? <| pure (hits.map copyEntry)
      finally withLookupPreparation budget? region.free
      pages := pages + 1
      for entry in hits do
        unless seen.contains (entry.module, entry.leanName) || index.excluded.any (fun n => n == entry.module.toName) do
          seen := seen.insert (entry.module, entry.leanName)
          entries := entries.push entry
    catch ex =>
      if ex.isMaxHeartbeat || ex.isInterrupt || ex.isRuntime then throw ex
      complete := false
      IO.eprintln s!"lookup.pickle_incomplete file={file} reason={← ex.toMessageData.toString}"
  let ordered := entries.qsort (fun a b =>
    if a.module != b.module then a.module < b.module else a.ordinal < b.ordinal)
  IO.eprintln s!"LOOKUP_COST backend=discrtree-pickle fallback={fallback} heartbeats={(← IO.getNumHeartbeats) - started} pages={pages} candidates={ordered.size}"
  return {complete, pages, entries := ordered}

end DiskLookup
end LeanInformationAudit.SearchReduction
