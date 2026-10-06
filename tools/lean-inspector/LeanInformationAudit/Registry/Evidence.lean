import LeanInformationAudit.Registry.Entries
import LeanInformationAudit.TemplateWire
import LeanInformationAudit.Registry.Repository
import LeanInformationAudit.CompiledEvidence
import Lean.Util.Heartbeats

namespace LeanInformationAudit.TemplateAudit
open Lean Meta

private def evidenceQuery (action : CompiledEvidence.Q α) : MetaM α := do
  let options ← getOptions
  let heartbeatStart ← getInitHeartbeats
  let heartbeatLimit ← getMaxHeartbeats
  RegistrationGates.Compiler.runQuery (fun context =>
    action.run { context with options, heartbeatStart, heartbeatLimit }) (← getLCtx)

def eraseProofs (e : Expr) (fuel : Nat := 524288) : MetaM (Expr × Nat) :=
  evidenceQuery (CompiledEvidence.eraseProofs e fuel)

def compactIdentity (params : List Name) (e : Expr) (fuel : Nat := 524288) : MetaM (Except String (String × Nat)) :=
  evidenceQuery (CompiledEvidence.compactIdentity params e fuel)

def statementDefinitions (statement : Expr) : MetaM (Array Name) :=
  evidenceQuery (CompiledEvidence.statementDefinitions statement)

def statementContainsOrigin (statement origin : Expr) : MetaM (Bool) :=
  evidenceQuery (CompiledEvidence.statementContainsOrigin statement origin)

def inspectionRoots (event : TemplateOccurrenceEvent) : MetaM (Array Name) :=
  evidenceQuery (CompiledEvidence.inspectionRoots event)

def inspectionDependencies (event : TemplateOccurrenceEvent) : MetaM (Array Name) :=
  evidenceQuery (CompiledEvidence.inspectionDependencies event)

def bridgeKind (event : TemplateOccurrenceEvent) : MetaM (String) :=
  evidenceQuery (CompiledEvidence.bridgeKind event)

def checkEscapeRecord (event : TemplateOccurrenceEvent) (input : EscapeRecordInput) : MetaM (EscapeRecordEvidence) :=
  evidenceQuery (CompiledEvidence.checkEscapeRecord event input)

def rawIdentity (params : List Name) (e : Expr) (fuel : Nat := 524288) : MetaM (Except String (String × Nat)) :=
  evidenceQuery (CompiledEvidence.rawIdentity params e fuel)

def escapeForwardBridge : Name := CompiledEvidence.escapeForwardBridge

def escapeWitnessBridge : Name := CompiledEvidence.escapeWitnessBridge

private abbrev HashWorker := IO.Process.Child {
  stdin := .piped, stdout := .piped, stderr := .null }

private initialize hashWorker : Std.Mutex (Option HashWorker) ← Std.Mutex.new none

/-- Reuse only the fixed worker process, never a file digest. Requests carry the
current repository root; copied oleans never retain the build host's root. The
mutex keeps each request/response together; any failure retires the stream. -/
private def fileInputBatch (paths : Array String) (readVersion : Bool := false) :
    IO (Array String × Option Nat) := do
  if paths.isEmpty && !readVersion then return (#[], none)
  let request := Json.arr #[toJson (← Repository.root).toString, toJson paths, toJson readVersion]
  hashWorker.atomically do
    try
      let child ← match ← get with
        | some child => pure child
        | none => do
          let child ← IO.Process.spawn {
            cmd := "python3", stdin := .piped, stdout := .piped, stderr := .null,
            args := #["-I", "-c",
              "import hashlib,json,pathlib,sys\n" ++
              "def unique(pairs):\n" ++
              " result={}\n" ++
              " for key,value in pairs:\n" ++
              "  if key in result: raise ValueError('duplicate field')\n" ++
              "  result[key]=value\n" ++
              " return result\n" ++
              "for line in sys.stdin.buffer:\n" ++
              " p=None\n" ++
              " try:\n" ++
              "  root,paths,read_version=json.loads(line)\n" ++
              "  hashes=[]; version=None\n" ++
              "  if read_version:\n" ++
              "   p='lean-report-inputs.json'\n" ++
              "   data=(pathlib.Path(root)/p).read_bytes()\n" ++
              "   version=json.loads(data.decode('utf-8'),object_pairs_hook=unique)['report_cache_release_semantic_version']\n" ++
              "   if type(version) is not int or version<=0: raise ValueError('version')\n" ++
              "  for p in paths:\n" ++
              "   hashes.append(hashlib.sha256((pathlib.Path(root)/p).read_bytes()).hexdigest())\n" ++
              "  result=[hashes,version]\n" ++
              " except Exception:\n" ++
              "  result='DTR-ManifestVersion' if p=='lean-report-inputs.json' else None\n" ++
              " print(json.dumps(result,separators=(',',':')),flush=True)\n"] }
          set (some child)
          pure child
      child.stdin.putStr (request.compress ++ "\n")
      child.stdin.flush
      let response ← IO.ofExcept <| Json.parse (← child.stdout.getLine)
      if response.getStr? == .ok "DTR-ManifestVersion" then
        throw <| IO.userError "DTR-ManifestVersion: missing or malformed report_cache_release_semantic_version"
      let (hashes, version) : Array String × Option Nat ← IO.ofExcept <| fromJson? response
      unless hashes.size == paths.size && hashes.all (fun hash => hash.length == 64 &&
          hash.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))) do
        throw <| IO.userError "incomplete_closure:E7.native_hash"
      return (hashes, version)
    catch error =>
      let child : Option HashWorker ← get
      set (none : Option HashWorker)
      if let some child := child then
        try child.kill catch _ => pure ()
        try discard <| child.wait catch _ => pure ()
      if error.toString.contains "DTR-ManifestVersion" then throw error
      throw <| IO.userError "incomplete_closure:E7.native_hash"

private def fileHashes (paths : Array String) : IO (Array String) := do
  return (← fileInputBatch paths).1

/-- Read the explicit report release version without hashing source files. -/
def readReportCacheReleaseVersion : CoreM Nat := do
  let (_, version) ← fileInputBatch #[] true
  let some version := version
    | throwError "DTR-ManifestVersion: missing report_cache_release_semantic_version"
  return version

/-- Hash every supplied current file in order, including repeated paths. The
fixed native worker avoids interpreting SHA-256 separately for every byte. -/
def readSourceInputs (paths : Array String) : CoreM (Array SourceInput) := do
  let hashes ← fileHashes paths
  return (paths.zip hashes).map fun (path, sha256) => { path, sha256 }

def readSourceInput (path : String) : CoreM SourceInput := do
  let hashes ← fileHashes #[path]
  return { path, sha256 := hashes[0]! }

/-- Preserve already captured bytes across native validation. Hashing the live
paths again could bind a later replacement to the earlier checked native image. -/
private def capturedHashes (inputs : Array ByteArray) : IO (Array String) :=
  IO.FS.withTempDir fun directory => do
    let paths ← inputs.mapIdxM fun index bytes => do
      let path := directory / s!"input{index}"
      IO.FS.writeBinFile path bytes
      pure path.toString
    fileHashes paths

namespace NativeCoherence

private structure Snapshot where
  inputs : Array SourceInput
  data : ModuleData

-- Decode the fixed-width lowercase wire hash without allocating a monadic
-- UInt64 fold step for every digit. Prefixes are exact Naturals; conversion at
-- the end has the same modulo-2^64 result as the original UInt64 arithmetic.
private def parseHash (text : String) : Except String UInt64 :=
  if text.utf8ByteSize != 16 then .error "incomplete_closure:E7.native_trace_hash"
  else
    let bytes := text.toUTF8
    let rec loop : Nat → Nat → Nat → Except String UInt64
      | 0, _, result => .ok result.toUInt64
      | remaining + 1, index, result =>
        let byte := bytes[index]!
        if 48 ≤ byte && byte ≤ 57 then
          loop remaining (index + 1) (result * 16 + (byte - 48).toNat)
        else if 97 ≤ byte && byte ≤ 102 then
          loop remaining (index + 1) (result * 16 + (byte - 87).toNat)
        else .error "incomplete_closure:E7.native_trace_hash"
    loop 16 0 0

private def binaryHash (bytes : ByteArray) : UInt64 := mixHash 1723 (hash bytes)
private def textHash (text : String) : UInt64 := mixHash 1723 (hash text.crlfToLf)

private def field (json : Json) (key : String) : CoreM Json :=
  ofExcept <| json.getObjVal? key

private partial def traceHash (value : Json) (depth : Nat := 0) : Except String UInt64 := do
  if depth > 256 then throw "incomplete_closure:E7.native_trace_depth"
  if let .str text := value then return ← parseHash text
  let inputs ← value.getArr?
  inputs.foldlM (init := 1723) fun result input => do
    let pair ← input.getArr?
    unless pair.size == 2 do throw "incomplete_closure:E7.native_trace_pair"
    return mixHash result (← traceHash pair[1]! (depth + 1))

private def child (value : Json) (caption : String) : CoreM Json := do
  let inputs ← ofExcept <| value.getArr?
  let matching := inputs.filter fun input =>
    (((input.getArr?).toOption.bind (·[0]?)).bind (·.getStr?.toOption)) == some caption
  unless matching.size == 1 do throwError "incomplete_closure:E7.native_trace_input:{caption}"
  let pair ← ofExcept <| matching[0]!.getArr?
  unless pair.size == 2 do throwError "incomplete_closure:E7.native_trace_pair"
  return pair[1]!

private structure ExportHash where
  arts : UInt64
  metaArts : UInt64
  allArts : UInt64
  publicTransitive : UInt64
  metaTransitive : UInt64
  allTransitive : UInt64
  transitive : UInt64

private initialize regionIndex : EnvExtension
    (Option (Array CompactedRegion × Std.HashMap String (Option CompactedRegion))) ←
  registerEnvExtension (pure none)

private def loadedRegion (env : Environment) (path : System.FilePath) : CoreM CompactedRegion := do
  let cached := regionIndex.getState (← getEnv)
  let index ← match cached with
    | some (regions, index) =>
      unless (unsafe ptrEq regions env.header.regions) do
        throwError "incomplete_closure:E7.native_regions"
      pure index
    | none =>
      let mut index : Std.HashMap String (Option CompactedRegion) := {}
      for region in env.header.regions do
        let key := region.filePath.toString
        index := index.insert key (if index.contains key then none else some region)
      modifyEnv fun current => regionIndex.setState current (some (env.header.regions, index))
      pure index
  let some (some region) := index[path.toString]?
    | throwError "incomplete_closure:E7.native_mapping:{path}"
  return region

private def moduleFile (env : Environment) (name : Name) : CoreM System.FilePath := do
  let path ← findOLean name
  if Repository.isModule name then discard <| loadedRegion env path
  return path

private structure Cache where
  snapshots : Std.HashMap Name Snapshot := {}
  closures : Std.HashMap Name (Array Name) := {}
  exports : Std.HashMap Name ExportHash := {}
  deriving Inhabited

private initialize checked : EnvExtension Cache ← registerEnvExtension (pure {})

private initialize observedInputs : EnvExtension (Array String) ← registerEnvExtension (pure #[])

/-- Read-only observation of the files rechecked by the latest selected validation. -/
def lastInputs (env : Environment) : Array String := observedInputs.getState env

/-- The pinned Lake import modifiers select both transitive and artifact traces. -/
private def importHashes (value : ExportHash) (nonModule : Bool) (imported : Import) :
    String × UInt64 × String × UInt64 :=
  if nonModule then ("legacy", value.transitive, "importAllArts", value.allArts)
  else if imported.importAll then ("all", value.allTransitive, "importAllArts", value.allArts)
  else if imported.isMeta then ("meta", value.metaTransitive, "importArts (meta)", value.metaArts)
  else ("public", value.publicTransitive, "importArts", value.arts)

/-- Reproduce Lake.Module.computeExportInfo's four import hash relations.
Compiler-owned imports have no Lake package trace and are pinned by the Lean
version input. Package traces remain trusted upstream build metadata. -/
private partial def exports (env : Environment) (name : Name)
    (memo : Std.HashMap Name ExportHash) : CoreM (Option ExportHash × Std.HashMap Name ExportHash) := do
  if let some value := memo[name]? then return (some value, memo)
  let artifact ← moduleFile env name
  let tracePath := artifact.withExtension "trace"
  if !(← tracePath.pathExists) then
    -- Lake supplies the compiler prefix to relocated inspector executables.
    -- Inside Lean itself the SDK build directory remains the fallback.
    let sysroot ← match ← IO.getEnv "LEAN_SYSROOT" with
      | some path => pure (System.FilePath.mk path)
      | none => getBuildDir
    let lib ← getLibDir sysroot
    unless (← IO.FS.realPath artifact).toString.startsWith ((← IO.FS.realPath lib).toString ++ "/") do
      throwError "incomplete_closure:E7.native_trace_missing:{name}"
    return (none, memo)
  let trace ← ofExcept <| Json.parse (← IO.FS.readFile tracePath)
  unless trace.getObjValAs? String "schemaVersion" == .ok "2025-09-10" do
    throwError "incomplete_closure:E7.native_trace_version:{name}"
  let output ← field trace "outputs"
  let oleans ← ofExcept <| output.getObjValAs? (Array String) "o"
  let isModule ← ofExcept <| output.getObjValAs? Bool "m"
  unless oleans.size == (if isModule then 3 else 1) do
    throwError "incomplete_closure:E7.native_trace_outputs:{name}"
  let mut parts := oleans
  if isModule then
    parts := parts.push (← ofExcept <| output.getObjValAs? String "rs")
    parts := parts.push (← ofExcept <| output.getObjValAs? String "r")
  let mut allArts := 1723
  for part in parts do
    allArts := mixHash allArts (← ofExcept <| parseHash (part.take 16).toString)
  let arts := mixHash 1723 (← ofExcept <| parseHash (oleans[0]!.take 16).toString)
  let mut metaArts := arts
  if isModule then
    for part in parts.extract 3 5 do
      metaArts := mixHash metaArts (← ofExcept <| parseHash (part.take 16).toString)
  let some index := env.getModuleIdx? name | throwError "incomplete_closure:E7.native_module:{name}"
  let data := env.header.moduleData[index.toNat]!
  let mut memo := memo
  let mut transitive := 1723
  let mut publicTransitive := 1723
  let mut metaTransitive := 1723
  let mut allTransitive := 1723
  for imported in data.imports do
    let (dependency, next) ← exports env imported.module memo
    memo := next
    if let some dependency := dependency then
      transitive := mixHash (mixHash transitive dependency.transitive) dependency.allArts
      metaTransitive := mixHash (mixHash metaTransitive dependency.metaTransitive) dependency.metaArts
      let (_, selected, _, selectedArts) := importHashes dependency false imported
      allTransitive := mixHash (mixHash allTransitive selected) selectedArts
      if imported.isExported then
        let selected := if imported.isMeta then dependency.metaTransitive
          else dependency.publicTransitive
        let selectedArts := if imported.isMeta then dependency.metaArts else dependency.arts
        publicTransitive := mixHash (mixHash publicTransitive selected) selectedArts
  let value : ExportHash := {
    arts := arts
    metaArts := metaArts
    allArts := allArts
    publicTransitive := publicTransitive
    metaTransitive := metaTransitive
    allTransitive := allTransitive
    transitive := transitive }
  return (some value, memo.insert name value)

private def unchanged (inputs : Array SourceInput) : IO Bool := do
  if inputs.isEmpty then return true
  let hashes ← fileHashes (inputs.map (·.path))
  return (inputs.zip hashes).all fun (input, hash) => input.sha256 == hash

/-- Exact runtime layout of the pinned compiler's CompactedRegion. Its private
root is a boxed ModuleData for the engine-loaded olean/IR parts selected below.
This cast never reads a fresh disk image or interprets a content-owned value. -/
private structure RegionLayout where
  filePath : System.FilePath
  size : USize
  isMemoryMapped : Bool
  baseAddr : USize
  bufferOffset : USize
  root : NonScalar

private unsafe def loadedPart (region : CompactedRegion) : ModuleData :=
  unsafeCast (unsafeCast region : RegionLayout).root

/-- The inspector links this fixed native comparison primitive. Interpreted
callers return zero and retain the serialization check below. The object-valued
Nat result and owned parameters match the interpreter's exported-function ABI. -/
@[noinline, export lean_dtr_mapped_image_match]
private unsafe def mappedImageMatch (_root : NonScalar) (_coordinates : Array USize)
    (_bytes : ByteArray) : Nat := 0

private unsafe def matchesLoadedImage (region : CompactedRegion) (bytes : ByteArray) : Bool :=
  let view : RegionLayout := unsafeCast region
  mappedImageMatch view.root #[view.size, view.baseAddr, view.bufferOffset,
    if view.isMemoryMapped then 1 else 0] bytes == 1

private def loadedIdentity (name : Name) (data : ModuleData) (bytes : ByteArray)
    (region : CompactedRegion) : IO String := do
  if (unsafe ptrEq data (loadedPart region)) && (unsafe matchesLoadedImage region bytes) then
    -- Hash the exact captured image, never a later read of its mutable path.
    return (← capturedHashes #[bytes])[0]!
  IO.FS.withTempFile fun _ path => do
    saveModuleData path name data
    unless (← IO.FS.readBinFile path) == bytes do
      throw <| IO.userError s!"incomplete_closure:E7.loaded_native:{name}"
    return (← fileHashes #[path.toString])[0]!

/-- Re-serialize the original loaded chains, including their cross-part sharing.
Missing private/server/IR regions remain incomplete; disk-only hashes cannot
substitute for a part that was not loaded into this Environment. -/
private def loadedModuleParts (env : Environment) (name : Name) (artifact : System.FilePath) :
    CoreM (Array SourceInput × Array UInt64) := do
  let mut inputs := #[]
  let mut hashes := #[]
  for (key, paths) in #[(name, #[artifact, artifact.addExtension "server",
      artifact.addExtension "private"]),
      (name ++ `ir, #[artifact.withExtension "ir.sig", artifact.withExtension "ir"])] do
    let mut parts : Array ModuleData := #[]
    for path in paths do
      let region ← loadedRegion env path
      parts := parts.push (unsafe loadedPart region)
    let (partInputs, partHashes) ← IO.FS.withTempDir (m := IO) fun temp => do
      let outputs := parts.mapIdx fun i data => (temp / s!"part{i}", data)
      saveModuleDataParts key outputs
      let identities ← fileHashes (outputs.map (·.1.toString))
      let mut inputs := #[]
      let mut hashes := #[]
      for ((input, output), identity) in (paths.zip (outputs.map (·.1))).zip identities do
        let bytes ← IO.FS.readBinFile input
        unless (← IO.FS.readBinFile output) == bytes do
          throw <| IO.userError s!"incomplete_closure:E7.loaded_native:{name}"
        inputs := inputs.push { path := input.toString, sha256 := identity : SourceInput }
        hashes := hashes.push (binaryHash bytes)
      return (inputs, hashes)
    inputs := inputs ++ partInputs
    hashes := hashes ++ partHashes
  return (inputs, hashes)

private def verifyImported (env : Environment) (name : Name)
    (hashes : Std.HashMap Name ExportHash) : CoreM Snapshot := do
  let some index := env.getModuleIdx? name | throwError "incomplete_closure:E7.native_module:{name}"
  let data := env.header.moduleData[index.toNat]!
  let artifact ← moduleFile env name
  let tracePath := artifact.withExtension "trace"
  let source := sourcePath name
  let sourceBytes ← IO.FS.readBinFile (← Repository.source source)
  let sourceText ← IO.FS.readFile (← Repository.source source)
  let traceBytes ← IO.FS.readBinFile tracePath
  let trace ← ofExcept <| Json.parse (← IO.FS.readFile tracePath)
  unless trace.getObjValAs? String "schemaVersion" == .ok "2025-09-10" &&
      trace.getObjValAs? Bool "synthetic" == .ok false do
    throwError "incomplete_closure:E7.native_trace_version:{name}"
  let inputs ← field trace "inputs"
  let compiler ← child inputs s!"Lean {Lean.versionStringCore}, commit {Lean.githash}"
  unless (← ofExcept <| traceHash compiler) == textHash Lean.githash do
    throwError "incomplete_closure:E7.native_compiler:{name}"
  let top ← ofExcept <| inputs.getArr?
  let candidates := top.filter fun input =>
    (((input.getArr?).toOption.bind (·[0]?)).bind (·.getStr?.toOption)).any fun caption =>
      caption == source || caption.endsWith ("/" ++ source)
  unless candidates.size == 1 do throwError "incomplete_closure:E7.native_source_input:{name}"
  let pair ← ofExcept <| candidates[0]!.getArr?
  unless pair.size == 2 && (← ofExcept <| traceHash pair[1]!) == textHash sourceText do
    throwError "incomplete_closure:E7.native_source:{name}"
  unless (← ofExcept <| traceHash inputs) ==
      (← ofExcept <| parseHash (← ofExcept <| trace.getObjValAs? String "depHash")) do
    throwError "incomplete_closure:E7.native_trace_integrity:{name}"
  let imports ← child (← child inputs "deps") "imports"
  -- Compare both the captions and hash values against the actual imported DAG;
  -- implementation must retain the ordered caption/value list, not only a count.
  let mut expectedImports : Array (String × UInt64) := #[]
  for imported in data.imports do
    if let some dependency := hashes[imported.module]? then
      let (caption, transitive, artCaption, arts) := importHashes dependency (!data.isModule) imported
      expectedImports := expectedImports.push
        (s!"{imported.module} transitive imports ({caption})", transitive)
      expectedImports := expectedImports.push (s!"{imported.module}:{artCaption}", arts)
  if expectedImports.isEmpty then
    unless (← ofExcept <| traceHash imports) == 1723 do
      throwError "incomplete_closure:E7.native_dependencies:{name}"
  else
    let rows ← ofExcept <| imports.getArr?
    unless rows.size == expectedImports.size do
      throwError "incomplete_closure:E7.native_dependencies:{name}"
    for (row, (caption, hash)) in rows.zip expectedImports do
      let pair ← ofExcept <| row.getArr?
      unless pair.size == 2 && pair[0]!.getStr? == .ok caption &&
          (← ofExcept <| traceHash pair[1]!) == hash do
        throwError "incomplete_closure:E7.native_dependency:{name}:{caption}"
  let (nativeInputs, nativeHashes) ← if data.isModule then loadedModuleParts env name artifact else do
    let bytes ← IO.FS.readBinFile artifact
    let nativeIdentity ← loadedIdentity name data bytes (← loadedRegion env artifact)
    pure (#[{path := artifact.toString, sha256 := nativeIdentity}], #[binaryHash bytes])
  let output ← field trace "outputs"
  let mut parts ← ofExcept <| output.getObjValAs? (Array String) "o"
  unless output.getObjValAs? Bool "m" == .ok data.isModule &&
      parts.size == (if data.isModule then 3 else 1) do
    throwError "incomplete_closure:E7.native_output:{name}"
  if data.isModule then
    parts := parts.push (← ofExcept <| output.getObjValAs? String "rs")
    parts := parts.push (← ofExcept <| output.getObjValAs? String "r")
  for (part, hash) in parts.zip nativeHashes do
    unless (← ofExcept <| parseHash (part.take 16).toString) == hash do
      throwError "incomplete_closure:E7.native_output:{name}"
  let sourceHashes ← capturedHashes #[sourceBytes, traceBytes]
  let result : Snapshot := { data, inputs := #[
    {path := source, sha256 := sourceHashes[0]!},
    {path := tracePath.toString, sha256 := sourceHashes[1]!}] ++ nativeInputs }
  -- Close source/artifact replacement during verification itself.
  unless ← unchanged result.inputs do
    throwError "incomplete_closure:E7.native_input_changed:{name}"
  return result

/-- Subsequent uses compare the immutable snapshot; they never issue a new
snapshot around a changed input in an already-loaded Environment. -/
private partial def collect (env : Environment) (root : Name) (seen : NameSet)
    (names : Array Name) : CoreM (NameSet × Array Name) := do
  if seen.contains root || !Repository.isModule root then return (seen, names)
  let seen := seen.insert root
  if root == env.header.mainModule then return (seen, names.push root)
  let imports ← do
    let some index := env.getModuleIdx? root | throwError "incomplete_closure:E7.native_module:{root}"
    pure env.header.moduleData[index.toNat]!.imports
  let mut seen := seen
  let mut names := names
  for imported in imports do
    let (nextSeen, nextNames) ← collect env imported.module seen names
    seen := nextSeen
    names := nextNames
  return (seen, names.push root)

/-- Validate selected source/native input closures. The current module is bound
by its parser input; only explicitly supplied imported owners are traversed.
Cached snapshots cannot be renewed around changed bytes in the same environment. -/
def validate (roots : Array Name) : CoreM Unit := do
  let profiling := (← IO.getEnv "STRATALINT_INSPECTOR_PROFILE") == some "1"
  let started ← if profiling then IO.monoNanosNow else pure 0
  let env ← getEnv
  let mut cache := checked.getState env
  let mut names : NameSet := {}
  for root in roots do
    let closure ← if let some closure := cache.closures[root]? then pure closure else do
      let (_, closure) ← collect env root {} #[]
      pure closure
    cache := { cache with closures := cache.closures.insert root closure }
    for name in closure do names := names.insert name
  let collected ← if profiling then IO.monoNanosNow else pure 0
  let mut exportNanos := 0
  let mut verifyNanos := 0
  let mut fresh := 0
  let mut retainedInputs : Array SourceInput := #[]
  for name in names do
    if name == env.header.mainModule then
      unless (← IO.FS.readFile (← Repository.source (sourcePath name))) == (← getFileMap).source do
        throwError "incomplete_closure:E7.current_source:{name}"
      continue
    if let some snapshot := cache.snapshots[name]? then
      let some index := env.getModuleIdx? name
        | throwError "incomplete_closure:E7.native_module:{name}"
      unless (unsafe ptrEq snapshot.data env.header.moduleData[index.toNat]!) do
        throwError "incomplete_closure:E7.native_environment:{name}"
    else
      let beforeExport ← if profiling then IO.monoNanosNow else pure 0
      let (_, next) ← exports env name cache.exports
      cache := { cache with exports := next }
      let beforeVerify ← if profiling then IO.monoNanosNow else pure 0
      let snapshot ← verifyImported env name cache.exports
      cache := { cache with snapshots := cache.snapshots.insert name snapshot }
      if profiling then
        exportNanos := exportNanos + beforeVerify - beforeExport
        verifyNanos := verifyNanos + (← IO.monoNanosNow) - beforeVerify
        fresh := fresh + 1
    let some snapshot := cache.snapshots[name]?
      | throwError "incomplete_closure:E7.native_snapshot:{name}"
    retainedInputs := retainedInputs ++ snapshot.inputs
  let beforeHashes ← if profiling then IO.monoNanosNow else pure 0
  unless ← unchanged retainedInputs do
    throwError "incomplete_closure:E7.native_input_changed"
  modifyEnv fun current => observedInputs.setState (checked.setState current cache)
    (retainedInputs.map (·.path))
  if profiling then
    let finished ← IO.monoNanosNow
    (← IO.getStderr).putStrLn s!"LEAN_INSPECTOR_PROFILE native_roots={roots.size} \
      fresh_modules={fresh} files={retainedInputs.size} closure_ns={collected - started} \
      export_ns={exportNanos} verify_ns={verifyNanos} rehash_ns={finished - beforeHashes} \
      total_ns={finished - started}"

end NativeCoherence

end LeanInformationAudit.TemplateAudit
