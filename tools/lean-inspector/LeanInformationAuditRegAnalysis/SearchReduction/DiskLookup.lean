import Lean

/-! Versioned, module-sharded disk retrieval. Keys only select candidates;
application and kernel checking remain the authority for successful queries. -/
namespace LeanInformationAudit.SearchReduction.DiskLookup
open Lean Meta

abbrev version : String := "disk-beta-zeta-alpha-v1"
abbrev pageSize : Nat := 256

structure Entry where
  module : String
  name : String
  deriving ToJson, FromJson, Inhabited

structure Page where
  file : String
  digest : UInt64
  count : Nat
  deriving ToJson, FromJson, Inhabited

structure Node where
  children : Array (String × String × UInt64) := #[]
  pages : Array Page := #[]
  deriving ToJson, FromJson, Inhabited

structure Header where
  format : String := version
  basis : String
  mathlib : String
  root : String
  digest : UInt64
  complete : Bool
  modules : Nat
  declarations : Nat
  indexed : Nat
  missing : Array String
  deriving ToJson, FromJson, Inhabited

structure Index where
  directory : System.FilePath
  header : Header
  excluded : Array Name := #[]

structure Candidates where
  entries : Array Entry := #[]
  complete : Bool := false
  pages : Nat := 0
  deriving Inhabited

private def readJson [FromJson α] (path : System.FilePath) : IO α := do
  IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse (← IO.FS.readFile path))

private def writeJson [ToJson α] (path : System.FilePath) (value : α) : IO UInt64 := do
  let text := (toJson value).compress
  IO.FS.writeFile path text
  return hash text

/-- Beta/zeta normal form with metadata, binder names and universe spellings
removed. Hash collisions always pass through definitional equality checking. -/
partial def canonical : Expr → Expr
  | .mdata _ e => canonical e
  | .letE _ _ v b _ => canonical (b.instantiate1 v)
  | .app f a =>
    let f := canonical f
    let a := canonical a
    if f.isLambda then canonical (f.bindingBody!.instantiate1 a) else mkApp f a
  | .lam _ t b _ => .lam .anonymous (canonical t) (canonical b) .default
  | .forallE _ t b _ => .forallE .anonymous (canonical t) (canonical b) .default
  | .const n ls => .const n (ls.map fun _ => .zero)
  | .sort _ => .sort .zero
  | .proj n i e => .proj n i (canonical e)
  | e => e

private def rigid : ConstantInfo → Bool
  | .inductInfo _ | .ctorInfo _ | .axiomInfo _ | .opaqueInfo _ | .thmInfo _ => true
  | _ => false

/-- A prefix discrimination path. Definition heads, projections, binders and
parameters are wildcards; this deliberately over-recalls reductions and
instantiations. Rigid constants retain application arity and nested structure. -/
partial def path (isRigid : Name → Bool) (e : Expr) (fuel : Nat := 8) : List String :=
  if fuel == 0 then ["*"] else
  let e := canonical e
  match e.getAppFn with
  | .const n _ =>
    if isRigid n then
      (s!"c:{e.getAppNumArgs}:{n}") ::
        e.getAppArgs.toList.flatMap (fun a => path isRigid a (fuel - 1))
    else ["*"]
  | _ => ["*"]

private partial def body : Expr → Expr
  | .forallE _ _ b _ => body b
  | .mdata _ b => body b
  | .letE _ _ v b _ => body (b.instantiate1 v)
  | e => e

private partial def conclusions (e : Expr) (fuel : Nat := 32) : Array Expr :=
  if fuel == 0 then #[] else
  let e := body e
  let result := #[e]
  if e.isAppOfArity ``And 2 then
    result ++ conclusions (e.getArg! 0) (fuel - 1) ++ conclusions (e.getArg! 1) (fuel - 1)
  else if e.isAppOfArity ``Iff 2 then
    result ++ conclusions (e.getArg! 0) (fuel - 1) ++ conclusions (e.getArg! 1) (fuel - 1)
  else if e.isAppOfArity ``Eq 3 then
    let result := result.push (mkAppN (e.getAppFn) #[e.getArg! 0, e.getArg! 2, e.getArg! 1])
    if e.getArg! 0 == mkSort .zero then result.push (mkBVar 0) else result
  else if e.isAppOfArity ``Subtype 2 then result.push (mkBVar 0)
  else result

private structure BuildNode where
  children : Std.HashMap String String := {}
  entries : Array Entry := #[]

private abbrev Nodes := Std.HashMap String BuildNode

private def insert (nodes : Nodes) (keys : List String) (entry : Entry) : Nodes := Id.run do
  let mut nodes := nodes
  let mut here := "root"
  for key in keys do
    let mut node := nodes[here]?.getD {}
    let next := s!"{here}/{key}"
    node := {node with children := node.children.insert key next}
    nodes := nodes.insert here node
    here := next
  let node := nodes[here]?.getD {}
  return nodes.insert here {node with entries := node.entries.push entry}

private def fileId (key : String) : String := toString (hash key)

private partial def flush (directory : System.FilePath) (nodes : Nodes) (key : String) : IO UInt64 := do
  let node := nodes[key]?.getD {}
  let mut children := #[]
  for (token, next) in node.children.toArray.qsort (fun a b => a.1 < b.1) do
    let digest ← flush directory nodes next
    children := children.push (token, fileId next, digest)
  let mut groups : Std.HashMap String (Array Entry) := {}
  for entry in node.entries do
    groups := groups.insert entry.module ((groups[entry.module]?.getD #[]).push entry)
  let mut pages := #[]
  for (owner, entries) in groups.toArray.qsort (fun a b => a.1 < b.1) do
    for offset in [: (entries.size + pageSize - 1) / pageSize] do
      let chunk := entries.extract (offset * pageSize) ((offset + 1) * pageSize)
      let file := s!"{fileId key}-{fileId owner}-{offset}.page.json"
      let digest ← writeJson (directory / file) chunk
      pages := pages.push {file, digest, count := chunk.size}
  writeJson (directory / s!"{fileId key}.node.json") ({children, pages} : Node)

private def runGit (args : Array String) : IO String := do
  let result ← IO.Process.output {cmd := "git", args}
  unless result.exitCode == 0 do throw <| IO.userError result.stderr
  return result.stdout.trimAscii.toString

/-- Read compiler module data without importing a full environment. All module
parts, including private declarations, participate in the coverage counts. -/
private def moduleParts (name : Name) : IO (Array (ModuleData × CompactedRegion)) := do
  let file ← findOLean name
  let main ← readModuleData file
  if !main.1.isModule then return #[main]
  readModuleDataParts #[file, OLeanLevel.server.adjustFileName file,
    OLeanLevel.private.adjustFileName file]

/-- Production inputs are protected frozen membership, the pinned Mathlib data
and the explicit format. Program bytes never enter the reuse identity. -/
unsafe def produce (directory : System.FilePath) (basis mathlib : String)
    (roots : Array Name) (checkSources : Bool := true) : IO Header := do
  IO.FS.createDirAll directory
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut rigidNames : NameSet := {}
  let mut reducibleNames : NameSet := {}
  let mut modules : Array Name := #[]
  let mut missing : Array String := #[]
  -- This first pass retains only names and rigid-symbol metadata.
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    try
      let parts ← moduleParts name
      for (part, _) in parts do
        for info in part.constants do
          if rigid info then rigidNames := rigidNames.insert info.name
          if let .defnInfo value := info then
            let mut body := value.value
            while body.isLambda do body := body.bindingBody!
            unless body.isProj || value.hints.isAbbrev do
              rigidNames := rigidNames.insert info.name
        for (extension, entries) in part.entries do
          if extension == `reducibilityCore then
            for entry in entries do
              let (n, status) : Name × ReducibilityStatus := unsafeCast entry
              if status == .reducible then reducibleNames := reducibleNames.insert n
        for dependency in part.imports do todo := todo.push dependency.module
      modules := modules.push name
    catch ex => missing := missing.push s!"{name}: {ex}"
  for n in reducibleNames do rigidNames := rigidNames.erase n
  let mut nodes : Nodes := {}
  let mut coverage : Array Json := #[]
  let mut declarations := 0
  let mut indexed := 0
  for name in modules.qsort Name.quickLt do
    try
      if checkSources && name.toString.startsWith "D5." then
        let source := name.toString.replace "." "/" ++ ".lean"
        let expected ← runGit #["rev-parse", s!"{basis}:{source}"]
        let actual ← runGit #["hash-object", source]
        unless expected == actual do throw <| IO.userError "source does not match protected basis"
      let parts ← moduleParts name
      let mut count := 0
      let mut localIndexed := 0
      for (part, _) in parts do
        for info in part.constants do
          count := count + 1
          let entry : Entry := {module := name.toString, name := info.name.toString}
          nodes := insert nodes ["member", toString (canonical info.type).hash] entry
          let mut paths : Std.HashSet (List String) := {}
          for view in conclusions info.type do
            paths := paths.insert (path rigidNames.contains view)
          -- A reducible result may expose conjunction/iff/subtype views.
          if (path rigidNames.contains (body info.type)).head? == some "*" then
            paths := paths.insert ["*"]
          for keys in paths do nodes := insert nodes ("candidate" :: keys) entry
          localIndexed := localIndexed + 1
      declarations := declarations + count
      indexed := indexed + localIndexed
      coverage := coverage.push <| Json.mkObj [("module", toJson name.toString),
        ("declarations", toJson count), ("indexed", toJson localIndexed)]
    catch ex => missing := missing.push s!"{name}: {ex}"
  let digest ← flush directory nodes "root"
  let header : Header := {
    basis, mathlib, root := fileId "root", digest,
    complete := missing.isEmpty && modules.size == seen.size,
    modules := modules.size, declarations, indexed, missing}
  discard <| writeJson (directory / "coverage.json") coverage
  -- Publication is the final operation. A failed producer cannot publish a
  -- complete header referring to unfinished pages.
  discard <| writeJson (directory / "header.json.tmp") header
  IO.FS.rename (directory / "header.json.tmp") (directory / "header.json")
  IO.println (toJson header).compress
  return header

def openIndex (directory : System.FilePath) (basis mathlib : String)
    (excluded : Array Name := #[]) : IO Index := do
  let header : Header ← readJson (directory / "header.json")
  unless header.format == version && header.basis == basis && header.mathlib == mathlib do
    throw <| IO.userError "lookup.index_snapshot_mismatch"
  return {directory, header, excluded}

private def readChecked [FromJson α] (path : System.FilePath) (digest : UInt64) : IO α := do
  let text ← IO.FS.readFile path
  unless hash text == digest do throw <| IO.userError s!"lookup.index_page_mismatch:{path}"
  IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse text)

private def arity (token : String) : Nat :=
  if token == "*" then 0 else ((token.splitOn ":")[1]?.bind String.toNat?).getD 0

private partial def skip (keys : List String) (pending : Nat) : List String :=
  if pending == 0 then keys else
  match keys with
  | [] => []
  | key :: rest => skip rest (pending - 1 + arity key)

private partial def collect (index : Index) (file : String) (digest : UInt64)
    (query : List String) (storedPending : Nat := 0) : IO Candidates := do
  let node : Node ← readChecked (index.directory / s!"{file}.node.json") digest
  let mut result : Candidates := {complete := true}
  if query.isEmpty && storedPending == 0 then
    for page in node.pages do
      let entries : Array Entry ← readChecked (index.directory / page.file) page.digest
      unless entries.size == page.count do throw <| IO.userError "lookup.index_page_count"
      result := {result with
        pages := result.pages + 1,
        entries := result.entries ++ entries.filter (fun e => !index.excluded.contains e.module.toName)}
  for (token, next, nextDigest) in node.children do
    let remaining? := if storedPending > 0 then
        some (query, storedPending - 1 + arity token)
      else match query with
        | [] => none
        | q :: qs =>
          if token == "*" then some (skip qs (arity q), 0)
          else if q == "*" then some (qs, arity token)
          else if q == token then some (qs, 0) else none
    if let some (remaining, pending) := remaining? then
      let found ← collect index next nextDigest remaining pending
      result := {result with
        entries := result.entries ++ found.entries,
        complete := result.complete && found.complete, pages := result.pages + found.pages}
  return result

/-- Missing or corrupt nodes/pages are incomplete, never certified negatives.
Only matching branches and necessary wildcard branches are read. -/
def query (index : Index) (keys : List String) : IO Candidates := do
  try
    let result ← collect index index.header.root index.header.digest keys
    let mut seen : NameSet := {}
    let mut entries := #[]
    for entry in result.entries do
      let name := entry.name.toName
      unless seen.contains name do entries := entries.push entry; seen := seen.insert name
    return {result with entries, complete := result.complete && index.header.complete}
  catch _ => return {}

def memberKeys (type : Expr) : List String := ["member", toString (canonical type).hash]

def candidateKeys (env : Environment) (type : Expr) : List String :=
  "candidate" :: path (fun n => (env.find? n).any (fun info =>
    if rigid info then true else
    match info with
    | .defnInfo _ => getReducibilityStatusCore env n != .reducible &&
        (env.getProjectionFnInfo? n).isNone
    | _ => false)) type

end LeanInformationAudit.SearchReduction.DiskLookup
