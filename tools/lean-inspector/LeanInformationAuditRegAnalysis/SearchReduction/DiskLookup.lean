import Lean
import Batteries.Util.Pickle
import Lean.Meta.DiscrTree

/-! Module-owned, versioned discrimination trees stored in compacted regions.
Only candidate certificates carry semantic authority. -/
namespace LeanInformationAudit.SearchReduction.DiskLookup
open Lean Meta

abbrev version : String := "R_lookup/discrtree-pickle-v4"

structure Entry where
  module : String
  name : String
  parts : Array (String × Nat)
  ordinal : Nat := 0
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

structure Index where
  directory : System.FilePath
  header : Header
  excluded : Array Name := #[]
  manifest : Array (UInt64 × Array String) := #[]

structure Candidates where
  entries : Array Entry := #[]
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
    try viewPaths type
    catch ex =>
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
          let entry : Entry := {
            module, name := ownedString info.name.toString,
            parts := nameParts info.name, ordinal := count}
          let paths ← pathsInEnvironment env stable.type s!"{module}:{info.name}"
          let mut seen : Std.HashSet (Array DiscrTree.Key) := {}
          for keys in paths do
            if seen.contains keys then continue
            seen := seen.insert keys
            let fallback := dropped keys
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
  let storage := directory / s!"discrtree-pickle-v4-{inputs}"
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
  return {directory := storage, header, excluded, manifest := manifest.roots}

/-- The persisted core tree is queried while its mmap is alive. Only detached
candidate metadata leaves the callback. Fallback is requested after primary
certificate attempts fail; an incomplete pass cannot certify NoHit. -/
unsafe def queryMature (index : Index) (type : Expr)
    (heartbeatLimit? : Option Nat := none) (fallback : Bool := false) : MetaM Candidates := do
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
      let hits : Array Entry ← withUnpickle (index.directory / file) fun (shard : PickledShard) => do
        let hits ← if fallback then pure shard.fallback else shard.tree.getMatch type
        return hits.map copyEntry
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

end LeanInformationAudit.SearchReduction.DiskLookup
