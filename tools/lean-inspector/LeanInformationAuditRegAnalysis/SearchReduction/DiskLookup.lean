import Lean

/-! Versioned, module-sharded disk retrieval. Keys only select candidates;
application and kernel checking remain the authority for successful queries. -/
namespace LeanInformationAudit.SearchReduction.DiskLookup
open Lean Meta

abbrev version : String := "disk-beta-zeta-alpha-v8"
abbrev pageSize : Nat := 256
abbrev keyDepth : Nat := 8

structure Entry where
  module : String
  name : String
  parts : Array (String × Nat)
  ordinal : Nat := 0
  route : String := ""
  deriving ToJson, FromJson, Inhabited

def Entry.leanName (entry : Entry) : Name :=
  entry.parts.foldl (fun parent (text, number) =>
    if number == 0 then .str parent text else .num parent (number - 1)) .anonymous

private def nameParts : Name → Array (String × Nat)
  | .anonymous => #[]
  | .str parent text => (nameParts parent).push (String.ofList text.toList, 0)
  | .num parent n => (nameParts parent).push ("", n + 1)

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
  let unchanged ← try pure ((← IO.FS.readFile path) == text) catch _ => pure false
  unless unchanged do IO.FS.writeFile path text
  return hash text

/-- Beta/zeta normal form with metadata, binder names and universe spellings
removed. Hash collisions always pass through definitional equality checking. -/
private partial def canonicalCached (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
  if let some found := (← get)[e]? then return found
  let result ← match e with
    | .mdata _ e => canonicalCached e
    | .letE _ _ v b _ => canonicalCached (b.instantiate1 v)
    | .app f a => do
      let f ← canonicalCached f
      let a ← canonicalCached a
      if f.isLambda then canonicalCached (f.bindingBody!.instantiate1 a) else pure (mkApp f a)
    | .lam _ t b _ => return .lam .anonymous (← canonicalCached t) (← canonicalCached b) .default
    | .forallE _ t b _ => return .forallE .anonymous (← canonicalCached t) (← canonicalCached b) .default
    | .const n ls => pure (.const n (ls.map fun _ => .zero))
    | .sort _ => pure (.sort .zero)
    | .proj n i e => return .proj n i (← canonicalCached e)
    | e => pure e
  modify (·.insert e result)
  return result

def canonical (e : Expr) : Expr := (canonicalCached e).run' {}

private def rigid : ConstantInfo → Bool
  | .inductInfo _ | .ctorInfo _ | .axiomInfo _ | .opaqueInfo _ | .thmInfo _ => true
  | _ => false

/-- A prefix discrimination path with application arities and binder positions.
Instantiable parameters, projection/reducible heads and the fixed depth boundary
are subtree wildcards. Binder names and telescope-variable indices cannot filter
candidates: instantiation and reordered telescopes are checked after retrieval.
Both producer and consumer use this exact, versioned shape. -/
private partial def pathCore (isRigid : Name → Bool) (e : Expr) (fuel : Nat) : List String :=
  if fuel == 0 then ["*"] else
  let e := e.eta
  match e with
  | .lam _ _ b _ => "l:1" :: pathCore isRigid b (fuel - 1)
  | .forallE _ t b _ => "f:2" ::
      (pathCore isRigid t (fuel - 1) ++ pathCore isRigid b (fuel - 1))
  | _ => match e.getAppFn with
    | .const n _ =>
      if isRigid n then
        (s!"c:{e.getAppNumArgs}:{n}") ::
          e.getAppArgs.toList.flatMap (fun a => pathCore isRigid a (fuel - 1))
      else ["*"]
    | _ => ["*"]

def path (isRigid : Name → Bool) (e : Expr) : List String :=
  pathCore isRigid (canonical e) keyDepth

private partial def body : Expr → Expr
  | .forallE _ _ b _ => body b
  | .mdata _ b => body b
  | .letE _ _ v b _ => body (b.instantiate1 v)
  | e => e

private partial def conclusions (e : Expr) (fuel : Nat := 32) : Array Expr :=
  if fuel == 0 then #[mkBVar 0] else
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

private structure Packed where
  directory : System.FilePath
  stem : String
  page : Nat := 0
  values : Array String := #[]
  bytes : Nat := 0

private def flushPack : StateT Packed IO Unit := do
  let state ← get
  unless state.values.isEmpty do
    discard <| writeJson (state.directory / s!"packs/{state.stem}-{state.page}.json") state.values
    set {state with page := state.page + 1, values := #[], bytes := 0}

/-- Physical pages hold at most 256 checked logical records. References retain
an individual record checksum, so packing changes neither keys nor candidates. -/
private def pack [ToJson α] (value : α) : StateT Packed IO (String × UInt64) := do
  let text := (toJson value).compress
  let state ← get
  if state.values.size >= pageSize || state.bytes + text.utf8ByteSize > 262144 then flushPack
  let state ← get
  let file := s!"packs/{state.stem}-{state.page}.json#{state.values.size}"
  set {state with values := state.values.push text, bytes := state.bytes + text.utf8ByteSize}
  return (file, hash text)

private structure BuildNode where
  children : Std.HashMap String String := {}
  entries : Array Entry := #[]
  pages : Array Page := #[]

private abbrev Nodes := Std.HashMap String BuildNode

private def insert (nodes : Nodes) (keys : List String) (entry : Entry) : Nodes := Id.run do
  let mut nodes := nodes
  let mut here := "root"
  for key in keys do
    let mut node := nodes[here]?.getD {}
    let next := s!"{hash (here, key)}"
    node := {node with children := node.children.insert key next}
    nodes := nodes.insert here node
    here := next
  let node := nodes[here]?.getD {}
  return nodes.insert here {node with entries := node.entries.push entry}

private def fileId (key : String) : String := toString (hash key)

/-- Statement-name payloads are spilled one module at a time. The producer
retains only trie routing and page descriptors across module boundaries. -/
private def spill (localNodes : Nodes) (all : Nodes) : StateT Packed IO Nodes := do
  let mut all := all
  for (key, node) in localNodes.toArray do
    let mut previous := all[key]?.getD {}
    for (token, next) in node.children.toArray do
      previous := {previous with children := previous.children.insert token next}
    let mut groups : Std.HashMap String (Array Entry) := {}
    for entry in node.entries do
      groups := groups.insert entry.module ((groups[entry.module]?.getD #[]).push entry)
    let mut pages := previous.pages
    for (_, entries) in groups.toArray.qsort (fun a b => a.1 < b.1) do
      for offset in [: (entries.size + pageSize - 1) / pageSize] do
        let chunk := entries.extract (offset * pageSize) ((offset + 1) * pageSize)
        let (file, digest) ← pack chunk
        pages := pages.push {file, digest, count := chunk.size}
    all := all.insert key {previous with pages}
  return all

private def routeByte (token : String) (depth : Nat) : Nat :=
  ((hash token >>> (depth * 8).toUInt64).toNat) % 256

/-- Routing directories have bounded fanout, including the membership hash
population. Wildcard queries enumerate only their necessary routing pages. -/
private partial def writeRouted (directory : System.FilePath) (file : String)
    (node : Node) (depth : Nat := 0) : IO UInt64 := do
  if node.children.size <= 256 then
    return ← writeJson (directory / s!"{file}.node.json") node
  if depth >= 8 then throw <| IO.userError "lookup.routing_hash_bucket_overflow"
  let mut groups : Std.HashMap Nat (Array (String × String × UInt64)) := {}
  for child in node.children do
    let bucket := routeByte child.1 depth
    groups := groups.insert bucket ((groups[bucket]?.getD #[]).push child)
  let mut children := #[]
  for (bucket, entries) in groups.toArray.qsort (fun a b => a.1 < b.1) do
    let next := s!"{file}.r{depth}-{bucket}"
    let digest ← writeRouted directory next {children := entries} (depth + 1)
    children := children.push (s!"@route:{depth}:{bucket}", next, digest)
  writeJson (directory / s!"{file}.node.json") {node with children}

private partial def repack (directory : System.FilePath) (file : String)
    (expected : UInt64) : StateT (Std.HashMap String UInt64) IO UInt64 := do
  if let some ready := (← get)[file]? then return ready
  let text ← IO.FS.readFile (directory / s!"{file}.node.json")
  unless hash text == expected do throw <| IO.userError "lookup.repack_checksum"
  let node : Node ← IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse text)
  let mut children := #[]
  for (token, next, digest) in node.children do
    let digest ← repack directory next digest
    children := children.push (token, next, digest)
  let digest ← writeRouted directory file {node with children}
  modify (·.insert file digest)
  return digest

private partial def flush (nodes : Nodes) (key : String) : StateT Packed IO (String × UInt64) := do
  let node := nodes[key]?.getD {}
  let mut children := #[]
  for (token, next) in node.children.toArray.qsort (fun a b => a.1 < b.1) do
    let (file, digest) ← flush nodes next
    children := children.push (token, file, digest)
  pack ({children, pages := node.pages} : Node)

private structure ModuleCheckpoint where
  name : String
  count : Nat
  offsets : Array (String × UInt64)
  deriving ToJson, FromJson

private def topKey (kind : String) : String := s!"{hash ("root", kind)}"

/-- A committed module records the durable ends of its bucket journals. On
restart, uncommitted journal tails are truncated before any module is retried. -/
private def restoreJournal (path : System.FilePath) (size : UInt64) : IO Unit := do
  if !(← path.pathExists) then
    unless size == 0 do throw <| IO.userError "lookup.checkpoint_missing_journal"
    IO.FS.writeFile path ""
  IO.FS.withFile path .readWrite fun handle => do
    let mut remaining := size.toNat
    while remaining > 0 do
      let bytes ← handle.read (min remaining 1048576).toUSize
      if bytes.isEmpty then throw <| IO.userError "lookup.checkpoint_short_journal"
      remaining := remaining - bytes.size
    handle.truncate

private def appendNodes (path : System.FilePath) (nodes : Nodes) : IO UInt64 := do
  let records := nodes.toArray.map fun (key, node) =>
    (key, ({children := node.children.toArray.map fun (token, next) =>
      (token, next, 0), pages := node.pages} : Node))
  IO.FS.withFile path .append fun handle => do
    handle.putStrLn (toJson records).compress
    handle.flush
  return (← path.metadata).byteSize

/-- Only one hash bucket is resident while global routing is assembled. The
module payload pages have already been committed and released. -/
private def finishBuckets (directory journals : System.FilePath) : IO UInt64 := do
  let mut rootChildren := #[]
  for kind in #["member", "candidate"] do
    let mut routes := #[]
    for bucket in [:256] do
      let journal := journals / s!"{kind}-{bucket}.jsonl"
      let nodes ← IO.FS.withFile journal .read fun handle => do
        let mut nodes : Nodes := {}
        repeat
          let line ← handle.getLine
          if line.isEmpty then break
          let records : Array (String × Node) ← IO.ofExcept <|
            fromJson? (← IO.ofExcept <| Json.parse line)
          for (key, node) in records do
            let mut previous := nodes[key]?.getD {}
            for (token, next, _) in node.children do
              previous := {previous with children := previous.children.insert token next}
            nodes := nodes.insert key {previous with pages := previous.pages ++ node.pages}
        return nodes
      let parent := nodes[topKey kind]?.getD {}
      let children ← (do
        let mut children := #[]
        for (token, next) in parent.children.toArray.qsort (fun a b => a.1 < b.1) do
          let (file, digest) ← flush nodes next
          children := children.push (token, file, digest)
        flushPack
        pure children).run' {directory, stem := s!"nodes-{kind}-{bucket}"}
      if !children.isEmpty then
        let file := s!"{fileId (topKey kind)}.r0-{bucket}"
        let digest ← writeRouted directory file {children} 1
        routes := routes.push (s!"@route:0:{bucket}", file, digest)
      if bucket % 32 == 0 then IO.eprintln s!"lookup.index_bucket={kind}:{bucket}"
    let file := fileId (topKey kind)
    let digest ← writeJson (directory / s!"{file}.node.json") ({children := routes} : Node)
    rootChildren := rootChildren.push (kind, file, digest)
  writeJson (directory / s!"{fileId "root"}.node.json") ({children := rootChildren} : Node)

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

private unsafe def summary (name : Name) : IO (Array Name × Array Name × Array Name × UInt64) :=
  visitModule name fun parts => do
    let mut deps := #[]
    let mut rigidNames := #[]
    let mut reducible := #[]
    let mut fingerprint : UInt64 := 0
    for part in parts do
      for info in part.constants do
        fingerprint := mixHash fingerprint (mixHash info.type.hash (hash info.value?))
        if rigid info then rigidNames := rigidNames.push (ownedName info.name)
        if let .defnInfo value := info then
          let mut body := value.value
          while body.isLambda do body := body.bindingBody!
          unless body.isProj || value.hints.isAbbrev do
            rigidNames := rigidNames.push (ownedName info.name)
      for (extension, entries) in part.entries do
        if extension == `reducibilityCore then
          for entry in entries do
            let (n, status) : Name × ReducibilityStatus := unsafeCast entry
            if status == .reducible then reducible := reducible.push (ownedName n)
      for dependency in part.imports do deps := deps.push (ownedName dependency.module)
    return (deps, rigidNames, reducible, fingerprint)

private unsafe def moduleEntries (name : Name) (rigidNames : NameSet) :
    IO (Array (List String × Entry) × Nat) :=
  visitModule name fun parts => do
    let mut entries := #[]
    let mut count := 0
    for part in parts do
      for info in part.constants do
        count := count + 1
        let entry : Entry := {
          module := name.toString, name := ownedString info.name.toString,
          parts := nameParts info.name, ordinal := count}
        entries := entries.push (["member", toString (canonical info.type).hash], entry)
        let mut paths : Std.HashSet (List String) := {}
        for view in conclusions info.type do
          paths := paths.insert (path rigidNames.contains view)
        for keys in paths do
          entries := entries.push ("candidate" :: keys, {entry with route := keys.head!})
    return (entries, count)

/-- Production inputs are protected frozen membership, compiled module data,
the pinned Mathlib data and explicit format. Program bytes are excluded. -/
unsafe def produce (directory : System.FilePath) (basis mathlib : String)
    (roots : Array Name) (checkSources : Bool := true) : IO Header := do
  IO.FS.createDirAll directory
  if checkSources then
    discard <| runGit #["diff", "--quiet", basis, "--", "D5"]
    let actual ← runGit #["-C", ".lake/packages/mathlib", "rev-parse", "HEAD"]
    unless actual == mathlib do throw <| IO.userError "lookup.mathlib_snapshot_mismatch"
  let basisModules := roots.foldl (fun set n => set.insert n) ({} : NameSet)
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut rigidNames : NameSet := {}
  let mut reducibleNames : NameSet := {}
  let mut modules : Array Name := #[]
  let mut missing : Array String := #[]
  let mut inputs : UInt64 := hash (version, basis, mathlib, Lean.versionString)
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    try
      let (deps, names, reducible, fingerprint) ← summary name
      inputs := mixHash inputs (mixHash (hash name) fingerprint)
      for n in names do rigidNames := rigidNames.insert n
      for n in reducible do reducibleNames := reducibleNames.insert n
      todo := todo ++ deps
      modules := modules.push name
      if modules.size % 1000 == 0 then IO.eprintln s!"lookup.index_summarized={modules.size}"
    catch ex => missing := missing.push s!"{name}: {ex}"
  for n in reducibleNames do rigidNames := rigidNames.erase n
  if missing.isEmpty then
    try
      let old : Header ← readJson (directory / "header.json")
      if old.format == version && old.basis == basis && old.mathlib == mathlib &&
          old.inputs == inputs && old.complete then
        IO.println (Json.mkObj [("reused", toJson true), ("header", toJson old)]).compress
        return old
    catch _ => pure ()
  let storage := s!"{version}-{inputs}"
  let pagesDirectory := directory / storage
  IO.FS.createDirAll (pagesDirectory / "packs")
  let journals := pagesDirectory / "stream-v1"
  IO.FS.createDirAll journals
  let selected := (modules.qsort Name.quickLt).filter fun name =>
    !name.toString.startsWith "D5." || basisModules.contains name
  let mut completed : Std.HashMap Name ModuleCheckpoint := {}
  let mut offsets : Std.HashMap String UInt64 := {}
  for name in selected do
    let path := journals / s!"{fileId name.toString}.checkpoint.json"
    if ← path.pathExists then
      let checkpoint : ModuleCheckpoint ← readJson path
      unless checkpoint.name == name.toString do throw <| IO.userError "lookup.checkpoint_module_mismatch"
      completed := completed.insert name checkpoint
      for (file, offset) in checkpoint.offsets do
        offsets := offsets.insert file (max offset (offsets[file]?.getD 0))
  for kind in #["member", "candidate"] do
    for bucket in [:256] do
      let file := s!"{kind}-{bucket}.jsonl"
      restoreJournal (journals / file) (offsets[file]?.getD 0)
  let mut coverage : Array Json := #[]
  let mut declarations := 0
  let mut indexed := 0
  for name in selected do
    try
      let checkpoint ← match completed[name]? with
        | some checkpoint => pure checkpoint
        | none => do
          let (entries, count) ← moduleEntries name rigidNames
          let mut groups : Std.HashMap String (Array (List String × Entry)) := {}
          for (keys, entry) in entries do
            let kind := keys.head!
            let token := keys[1]!
            let file := s!"{kind}-{routeByte token 0}.jsonl"
            groups := groups.insert file ((groups[file]?.getD #[]).push (keys, entry))
          let ends ← (do
            let mut ends := #[]
            for (file, group) in groups.toArray do
              let mut nodes : Nodes := {}
              for (keys, entry) in group do nodes := insert nodes keys entry
              let spilled ← spill nodes {}
              ends := ends.push (file, ← appendNodes (journals / file) spilled)
            flushPack
            pure ends).run' {directory := pagesDirectory, stem := s!"module-{fileId name.toString}"}
          let checkpoint : ModuleCheckpoint := {name := name.toString, count, offsets := ends}
          let path := journals / s!"{fileId name.toString}.checkpoint.json"
          discard <| writeJson (path.addExtension "tmp") checkpoint
          IO.FS.rename (path.addExtension "tmp") path
          pure checkpoint
      declarations := declarations + checkpoint.count
      indexed := indexed + checkpoint.count
      coverage := coverage.push <| Json.mkObj [("module", toJson name.toString),
        ("declarations", toJson checkpoint.count), ("indexed", toJson checkpoint.count)]
      if coverage.size % 100 == 0 then IO.eprintln s!"lookup.index_written={coverage.size},module={name},declarations={declarations}"
    catch ex =>
      missing := missing.push s!"{name}: {ex}"
      -- A failed module may have appended uncommitted tails. Stop instead of
      -- letting later commits make those tails part of a complete journal.
      break
  let digest ← finishBuckets pagesDirectory journals
  let header : Header := {
    basis, mathlib, inputs, storage, root := fileId "root", digest,
    complete := missing.isEmpty && modules.size == seen.size && coverage.size == selected.size,
    modules := modules.size, declarations, indexed, missing}
  discard <| writeJson (directory / "coverage.json") coverage
  discard <| writeJson (directory / "header.json.tmp") header
  IO.FS.rename (directory / "header.json.tmp") (directory / "header.json")
  IO.println (toJson header).compress
  return header

def openIndex (directory : System.FilePath) (basis mathlib : String)
    (excluded : Array Name := #[]) : IO Index := do
  let header : Header ← readJson (directory / "header.json")
  unless header.format == version && header.basis == basis && header.mathlib == mathlib do
    throw <| IO.userError "lookup.index_snapshot_mismatch"
  return {directory := directory / header.storage, header, excluded}

private structure PackedPage where
  bytes : ByteArray
  spans : Array (Nat × Nat)

private partial def packedSpans (bytes : ByteArray) (i start : Nat)
    (quoted escaped : Bool) (spans : Array (Nat × Nat)) : Option (Array (Nat × Nat)) :=
  if i >= bytes.size then if quoted then none else some spans
  else
    let byte := bytes[i]!
    if quoted then
      if escaped then packedSpans bytes (i + 1) start true false spans
      else if byte == 92 then packedSpans bytes (i + 1) start true true spans
      else if byte == 34 then packedSpans bytes (i + 1) start false false (spans.push (start, i + 1))
      else packedSpans bytes (i + 1) start true false spans
    else if byte == 34 then packedSpans bytes (i + 1) i true false spans
    else if byte == 91 || byte == 93 || byte == 44 || byte == 32 ||
        byte == 10 || byte == 13 || byte == 9 then
      packedSpans bytes (i + 1) start false false spans
    else none

private def packedPage (bytes : ByteArray) : Except String PackedPage := do
  let some spans := packedSpans bytes 0 0 false false #[]
    | throw "lookup.invalid_packed_page"
  return {bytes, spans}

private structure ReadCache where
  records : Std.HashMap String PackedPage := {}
  bytes : Nat := 0

private def readChecked [FromJson α] (cache : IO.Ref ReadCache)
    (path : System.FilePath) (digest : UInt64) : IO α := do
  let parts := path.toString.splitOn "#"
  let (file, slot?) := if parts.length > 1 then
      match parts.getLast!.toNat? with
      | some slot => (System.FilePath.mk (String.intercalate "#" parts.dropLast), some slot)
      | none => (path, none)
    else (path, none)
  let text ← match slot? with
    | none => IO.FS.readFile file
    | some slot => do
      let records ← match (← cache.get).records[file.toString]? with
        | some records => pure records
        | none => do
          let physical ← IO.FS.readBinFile file
          let records ← IO.ofExcept (packedPage physical)
          -- Packed records share a physical page. Decode that page once,
          -- retaining at most 16 MiB of page payload within this query.
          cache.modify fun old =>
            let old := if old.bytes + physical.size > 16777216 then {} else old
            {records := old.records.insert file.toString records,
             bytes := old.bytes + physical.size}
          pure records
      let some (start, stop) := records.spans[slot]? | throw <| IO.userError "lookup.packed_record_missing"
      let some encoded := String.fromUTF8? (records.bytes.extract start stop)
        | throw <| IO.userError "lookup.invalid_packed_utf8"
      IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse encoded)
  unless hash text == digest do throw <| IO.userError s!"lookup.index_page_mismatch:{path}"
  IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse text)

private def nodePath (directory : System.FilePath) (file : String) : System.FilePath :=
  if (file.splitOn "#").length > 1 && (file.splitOn "#").getLast!.toNat?.isSome then
    directory / file
  else directory / s!"{file}.node.json"

private partial def routedChildren (cache : IO.Ref ReadCache) (index : Index) (node : Node)
    (wanted : Option (List String)) : IO (Array (String × String × UInt64)) := do
  let mut children := #[]
  for child in node.children do
    let (token, next, digest) := child
    if token.startsWith "@route:" then
      let [_, depthText, bucketText] := token.splitOn ":"
        | throw <| IO.userError "lookup.invalid_routing_page"
      let some depth := depthText.toNat? | throw <| IO.userError "lookup.invalid_routing_depth"
      let some bucket := bucketText.toNat? | throw <| IO.userError "lookup.invalid_routing_bucket"
      if wanted.any (fun keys => !keys.any (fun key => routeByte key depth == bucket)) then continue
      let page : Node ← readChecked cache (nodePath index.directory next) digest
      children := children ++ (← routedChildren cache index page wanted)
    else if wanted.all (·.contains token) then children := children.push child
  return children.qsort (fun a b => a.1 < b.1)

private def arity (token : String) : Nat :=
  if token == "*" then 0 else ((token.splitOn ":")[1]?.bind String.toNat?).getD 0

private partial def skip (keys : List String) (pending : Nat) : List String :=
  if pending == 0 then keys else
  match keys with
  | [] => []
  | key :: rest => skip rest (pending - 1 + arity key)

private partial def collect (cache : IO.Ref ReadCache) (index : Index) (file : String) (digest : UInt64)
    (query : List String) (storedPending : Nat := 0) : IO Candidates := do
  let node : Node ← readChecked cache (nodePath index.directory file) digest
  let mut result : Candidates := {complete := true}
  if query.isEmpty && storedPending == 0 then
    for page in node.pages do
      let entries : Array Entry ← readChecked cache (index.directory / page.file) page.digest
      unless entries.size == page.count do throw <| IO.userError "lookup.index_page_count"
      result := {result with
        pages := result.pages + 1,
        entries := result.entries ++ entries.filter (fun e => !index.excluded.contains e.module.toName)}
  let wanted := if storedPending > 0 || query.head? == some "*" then none
    else some (match query with | [] => [] | q :: _ => [q, "*"])
  for (token, next, nextDigest) in (← routedChildren cache index node wanted) do
    let remaining? := if storedPending > 0 then
        some (query, storedPending - 1 + arity token)
      else match query with
        | [] => none
        | q :: qs =>
          if token == "*" then some (skip qs (arity q), 0)
          else if q == "*" then some (qs, arity token)
          else if q == token then some (qs, 0) else none
    if let some (remaining, pending) := remaining? then
      let found ← collect cache index next nextDigest remaining pending
      result := {result with
        entries := result.entries ++ found.entries,
        complete := result.complete && found.complete, pages := result.pages + found.pages}
  return result

/-- Missing or corrupt nodes/pages are incomplete, never certified negatives.
Only matching branches and necessary wildcard branches are read. -/
def query (index : Index) (keys : List String) : IO Candidates := do
  let started ← IO.monoMsNow
  let heartbeats ← IO.getNumHeartbeats
  try
    let cache ← IO.mkRef ({} : ReadCache)
    let result ← collect cache index index.header.root index.header.digest keys
    let mut seen : NameSet := {}
    let mut entries := #[]
    -- Refining the key filters the old depth-one enumeration; it must not
    -- prioritize candidates by their newly visible nested shape.
    let ordered := result.entries.qsort fun a b =>
      if a.route != b.route then a.route < b.route
      else if a.module != b.module then Name.quickLt a.module.toName b.module.toName
      else a.ordinal < b.ordinal
    for entry in ordered do
      let name := entry.leanName
      unless seen.contains name do entries := entries.push entry; seen := seen.insert name
    if (← IO.getEnv "SEARCH_REDUCTION_PROFILE").isSome then
      IO.eprintln s!"LOOKUP_COST index_ms={(← IO.monoMsNow) - started} heartbeats={(← IO.getNumHeartbeats) - heartbeats} pages={result.pages} candidates={entries.size}"
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
