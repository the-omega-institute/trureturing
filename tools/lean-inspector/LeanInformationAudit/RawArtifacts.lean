import LeanInformationAudit.Contract.SourceAudit
import LeanInformationAudit.CompiledMetadata
import Lean.Environment

open Lean

namespace LeanInformationAudit.RawArtifacts

/-- Opt-in operation context, carried only by the native producer's existing IO. -/
structure OperationObservation where
  request : String
  target : String
  producerPid : UInt32
  sequence : IO.Ref Nat
  parent : Nat := 0
  readKind : String := "first-read"

def operationObservation (target : String) : IO (Option OperationObservation) := do
  unless (← IO.getEnv "STRATALINT_INSPECTOR_OPERATIONS") == some "1" do return none
  let some request ← IO.getEnv "STRATALINT_INSPECTOR_OPERATION_REQUEST" | return none
  return some { request, target, producerPid := ← IO.Process.getPID, sequence := ← IO.mkRef 0 }

private def operationEvent (context : OperationObservation) (call : Nat)
    (operation : String) (module : Name) (part path outcome : String)
    (error : String := "") : IO Unit := do
  try
    let out ← IO.getStderr
    out.putStrLn <| "LEAN_INSPECTOR_OPERATION " ++ (Json.mkObj [
      ("request_id", toJson context.request), ("target", toJson context.target),
      ("producer_pid", toJson context.producerPid.toNat), ("monotonic_ns", toJson (← IO.monoNanosNow)),
      ("call", toJson call), ("parent_call", toJson context.parent),
      ("operation", toJson operation), ("module", toJson module.toString),
      ("part", toJson part), ("path", toJson path), ("read_kind", toJson context.readKind),
      ("outcome", toJson outcome), ("error", toJson error)]).compress
    out.flush
  catch _ => pure ()

/-- An entry without a return/error after supervisor termination is unresolved.
Observation failures do not replace the operation's result or exception. -/
def observeOperation {α : Type} (context : Option OperationObservation)
    (operation : String) (module : Name) (part : String)
    (action : Option OperationObservation → IO α) (path : String := "") : IO α := do
  let some context := context | return ← action none
  let call ← context.sequence.modifyGet fun value => (value + 1, value + 1)
  operationEvent context call operation module part path "entry"
  try
    let result ← action (some { context with parent := call })
    operationEvent context call operation module part path "return"
    return result
  catch error =>
    operationEvent context call operation module part path "error" error.toString
    throw error

/-- The pinned compiler's private declaration view, without an Environment or
extension state. Each store owns only the regions loaded into that store. -/
structure Store where
  modules : NameMap ModuleData := {}
  constants : SMap Name ConstantInfo := {}
  owners : SMap Name Name := {}
  moduleOrder : Array Name := #[]
  moduleIndices : Std.TreeMap Name Nat Name.quickCmp := {}
  protectedModules : Std.TreeMap Name Bool Name.quickCmp := {}
  metadata : CompiledMetadata.Store := {}
  active : NameSet := {}
  regions : Array CompactedRegion := #[]

/-- Compiler indexes keep their immutable imported table and put target additions
in Lean's existing persistent hash stage. No Environment is constructed. -/
def Store.fork (base : Store) : Store :=
  { base with constants := base.constants.switch, owners := base.owners.switch, regions := #[] }

def mapSize {α : Type} (map : SMap Name α) : Nat :=
  map.map₂.foldl (fun count name _ => if map.map₁.contains name then count else count + 1) map.map₁.size

private def checkHeader (path : System.FilePath) : IO Unit := do
  IO.FS.withFile path .read fun file => do
    let header ← file.read 88
    unless header.size == 88 && (header.extract 0 5) == "olean".toUTF8 do
      throw <| IO.userError s!"raw.invalid_header:{path}"
    unless header[5]! == 2 && header[6]! ≤ 1 do
      throw <| IO.userError s!"raw.unknown_format:{path}"
    unless (header.extract 7 40) == (versionString.toUTF8 ++ ByteArray.mk
        (Array.replicate (33 - versionString.utf8ByteSize) 0))
        && (header.extract 40 80) == githash.toUTF8 do
      throw <| IO.userError s!"raw.compiler_identity:{path}"

private def isPropCheap (find : Name → Option ConstantInfo) (type : Expr) : Bool := Id.run do
  let mut type := type
  while type.isForall do type := type.bindingBody!
  let .const name .. := type.getAppFn | return false
  let some info := find name | return false
  let mut result := info.type
  for _ in [:type.getAppNumArgs] do
    unless result.isForall do return false
    result := result.bindingBody!
  return result.isProp

/-- Same duplicate-theorem preference as the pinned compiler's private import
view; different definitions or incompatible duplicates are rejected. -/
private def subsumes (constants : SMap Name ConstantInfo)
    (left right : ConstantInfo) : Bool :=
  left.name == right.name && left.type == right.type && left.levelParams == right.levelParams &&
    match left, right with
    | .thmInfo a, .thmInfo b => a.all == b.all
    | .thmInfo a, .axiomInfo b => a.all == [b.name] && !b.isUnsafe
    | .axiomInfo a, .axiomInfo b => a.isUnsafe == b.isUnsafe && isPropCheap constants.find? a.type
    | _, _ => false

private unsafe def readOwnParts (name : Name) (observation : Option OperationObservation) :
    IO (ModuleData × Array CompactedRegion) := do
  let path ← try observeOperation observation "findOLean" name "base" (fun _ => findOLean name) catch error =>
    throw <| IO.userError s!"raw.missing_olean:{name}:{error}"
  -- Read the base first to determine whether the complete module-system
  -- chain is required. A private part may borrow objects from both earlier parts.
  observeOperation observation "header" name "base" (fun _ => checkHeader path) path.toString
  let base ← observeOperation observation "CompactedRegion.read" name "base"
    (fun _ => readModuleDataParts #[path]) path.toString
  let mut parts := base
  let some first := base[0]?
    | throw <| IO.userError s!"raw.empty_parts:{name}"
  if first.1.isModule then
    for suffix in ["server", "private"] do
      let part := path.addExtension suffix
      unless ← observeOperation observation "part-find" name suffix
          (fun _ => part.pathExists) part.toString do
        throw <| IO.userError s!"raw.missing_olean_part:{name}:{suffix}"
      observeOperation observation "header" name suffix (fun _ => checkHeader part) part.toString
      parts := parts.push (← observeOperation observation "CompactedRegion.read" name suffix
        (fun _ => CompactedRegion.read (α := ModuleData) part (parts.map (·.2))) part.toString)
  let some last := parts.back?
    | throw <| IO.userError s!"raw.empty_parts:{name}"
  let data := last.1
  observeOperation observation "constant-table-validation" name "all" fun _ => do
    unless data.constNames == data.constants.map (·.name) do
      throw <| IO.userError s!"raw.invalid_constant_table:{name}"
  return (data, parts.map (·.2))

unsafe def readOwn (name : Name) (observation : Option OperationObservation := none) :
    IO (ModuleData × Array CompactedRegion) := do
  try readOwnParts name observation
  catch error => throw <| IO.userError s!"raw.read_failed:{name}:{error}"

/-- The exact compiler heads of the input-projection wire schema. An owner
cannot select the compiled-only route by supplying an empty projection. -/
def hasTypedInputs (data : ModuleData) : Bool :=
  data.constants.any Contract.SourceAudit.isInput

/-- Cross-target keys must not borrow strings or parents from an olean region. -/
def ownName : Name → Name
  | .anonymous => .anonymous
  | .str parent text => .str (ownName parent) (String.ofList text.toList)
  | .num parent index => .num (ownName parent) ((toString index).toNat!)

@[noinline] private unsafe def importFact (name : Name) :
    IO (Array Name × Bool × Array CompactedRegion) := do
  let (data, regions) ← readOwn name
  let imports := data.imports.foldl (fun names item => names.push (ownName item.module)) #[]
  return (imports, hasTypedInputs data, regions)

-- mkModuleData preserves env.header at every olean level. Dependency planning
-- therefore needs only the base part, without touching imported constant tables.
@[noinline] private unsafe def importHeader (name : Name) :
    IO (Array Name × Array CompactedRegion) := do
  let path ← try findOLean name catch error =>
    throw <| IO.userError s!"raw.missing_olean:{name}:{error}"
  checkHeader path
  let (data, region) ← readModuleData path
  let imports := data.imports.foldl (fun names item => names.push (ownName item.module)) #[]
  return (imports, #[region])

/-- Only detached import names and input flags survive this planning pass.
The shared set is fixed before assessment and is closed under imports. -/
unsafe def sharedModules (targets : Array (Name × Array Name)) (statementOnly : Bool) :
    IO NameSet := do
  if targets.size ≤ 1 then return {}
  let facts ← IO.mkRef ({} : NameMap (Array Name × Bool))
  for (target, _) in targets do
    let (imports, typed, regions) ← importFact target
    for region in regions.reverse do region.free
    facts.modify (·.insert target (imports, typed))
  let visits ← IO.mkRef ({} : NameMap (Nat × Bool))
  let rec visit (target : Nat) (name : Name) : IO Unit := do
    let previous := (← visits.get).find? name
    if previous.any (fun item => item.1 == target || item.2) then return
    visits.modify (·.insert name (target, previous.isSome))
    let fact ← match (← facts.get).find? name with
      | some fact => pure fact
      | none => do
        let (imports, regions) ← importHeader name
        for region in regions.reverse do region.free
        facts.modify (·.insert name (imports, false))
        pure (imports, false)
    for dependency in fact.1 do visit target dependency
  for index in [:targets.size] do
    let (target, claims) := targets[index]!
    visit index target
    for claim in claims do visit index claim
    if !statementOnly && ((← facts.get).find? target).any (·.2) then
      visit index `LeanInformationAudit.TemplateEnrollment
  return (← visits.get).foldl (fun shared name item =>
    if item.2 then shared.insert name else shared) {}

/-- Empty the last owning root before the caller frees any mapped contents.
The noinline return boundary also destroys the store's metadata and maps. -/
@[noinline] def takeRegions (store : IO.Ref Store) : IO (Array CompactedRegion) :=
  store.modifyGet fun current => (current.regions, {})

unsafe def release (store : IO.Ref Store) : IO Unit := do
  let regions ← takeRegions store
  for region in regions.reverse do region.free

/-- Dependency-first compiler ownership facts, indexed while reading each module.
Missing import metadata cannot justify an external provenance leaf. -/
def moduleIsProtected (name : Name) (data : ModuleData)
    (classes : Std.TreeMap Name Bool Name.quickCmp) : Bool :=
  name.getRoot == `D5 || name.getRoot == `LeanInformationAudit ||
    data.imports.any (fun item => classes[item.module]?.getD true)

unsafe def loadModule (name : Name) (store : IO.Ref Store)
    (observation : Option OperationObservation := none) : IO Unit := do
  let state ← store.get
  if state.modules.contains name then return
  if state.active.contains name then
    throw <| IO.userError s!"raw.import_cycle:{name}"
  observeOperation observation "load-module" name "all" fun observation => do
    store.modify fun s => { s with active := s.active.insert name }
    let (data, regions) ← readOwn name observation
    store.modify fun s => { s with regions := s.regions ++ regions }
    for item in data.imports do loadModule item.module store observation
    let constants ← observeOperation observation "constant-merge" name "all" fun _ => do
      let mut constants ← store.modifyGet fun s => (s.constants, { s with constants := {} })
      for info in data.constants do
        if let some previous := constants.find? info.name then
          if subsumes constants info previous then constants := constants.insert info.name info
          else unless subsumes constants previous info do
            throw <| IO.userError s!"raw.conflicting_constant:{name}:{info.name}"
        else constants := constants.insert info.name info
      return constants
    observeOperation observation "index-metadata" name "all" fun _ => do
      store.modify fun s =>
        let moduleIndices := s.moduleIndices.insert name s.moduleOrder.size
        { s with
        constants := constants
        owners := data.constNames.foldl (fun owners constant => if owners.contains constant then owners else owners.insert constant name) s.owners
        modules := s.modules.insert name data
        moduleIndices
        protectedModules := s.protectedModules.insert name (moduleIsProtected name data s.protectedModules)
        moduleOrder := s.moduleOrder.push name
        metadata := CompiledMetadata.readModule s.metadata data
        active := s.active.erase name }

@[noinline] private unsafe def comparePrevious (owner : Name) (info : ConstantInfo)
    (constants : SMap Name ConstantInfo) (observation : Option OperationObservation) :
    IO (Bool × Array CompactedRegion) := do
  let observation := observation.map fun context => { context with readKind := "collision-reread" }
  observeOperation observation "comparePrevious" owner "all" fun observation => do
    let (data, regions) ← readOwn owner observation
    let compatible := (data.constants.find? (·.name == info.name)).any fun previous =>
      subsumes constants info previous || subsumes constants previous info
    return (compatible, regions)

/-- Preserve the union reader's duplicate checks without retaining old terms.
Only detached declaration/owner names survive; a collision rereads its owner. -/
unsafe def checkBatchConstants (base store : Store) (seen : IO.Ref (NameMap Name))
    (observation : Option OperationObservation := none) : IO Unit := do
  -- Target loading appends to the fixed base's module order.
  for index in [base.moduleOrder.size:store.moduleOrder.size] do
    let owner := store.moduleOrder[index]!
    let ownedOwner := ownName owner
    let some data := store.modules.find? owner
      | throw <| IO.userError s!"raw.missing_module:{owner}"
    for info in data.constants do
      if let some previous := (← seen.get).find? info.name then
        if previous != owner then
          let (compatible, regions) ← comparePrevious previous info store.constants observation
          for region in regions.reverse do region.free
          unless compatible do
            throw <| IO.userError s!"raw.conflicting_constant:{owner}:{info.name}"
      else seen.modify (·.insert (ownName info.name) ownedOwner)

def Store.getModule (store : Store) (name : Name) : IO ModuleData := do
  let some data := store.modules.find? name
    | throw <| IO.userError s!"raw.missing_module:{name}"
  return data

def getConstant (find : Name → Option ConstantInfo) (name : Name) : IO ConstantInfo := do
  let some info := find name
    | throw <| IO.userError s!"raw.incomplete_closure:{name}"
  return info

end LeanInformationAudit.RawArtifacts
