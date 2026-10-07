import LeanInformationAudit.Contract.SourceAudit
import LeanInformationAudit.CompiledMetadata
import Lean.Environment

open Lean

namespace LeanInformationAudit.RawArtifacts

/-- The pinned compiler's private declaration view, without an Environment or
extension state. Regions remain live for the lifetime of the reader process. -/
structure Store where
  modules : NameMap ModuleData := {}
  constants : Std.HashMap Name ConstantInfo := {}
  owners : Std.HashMap Name Name := {}
  moduleOrder : Array Name := #[]
  metadata : CompiledMetadata.Store := {}
  active : NameSet := {}
  regions : Array CompactedRegion := #[]

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
private def subsumes (constants : Std.HashMap Name ConstantInfo)
    (left right : ConstantInfo) : Bool :=
  left.name == right.name && left.type == right.type && left.levelParams == right.levelParams &&
    match left, right with
    | .thmInfo a, .thmInfo b => a.all == b.all
    | .thmInfo a, .axiomInfo b => a.all == [b.name] && !b.isUnsafe
    | .axiomInfo a, .axiomInfo b => a.isUnsafe == b.isUnsafe && isPropCheap (constants[·]?) a.type
    | _, _ => false

private unsafe def readOwnParts (name : Name) : IO (ModuleData × Array CompactedRegion) := do
  let path ← try findOLean name catch error =>
    throw <| IO.userError s!"raw.missing_olean:{name}:{error}"
  -- Read the base first to determine whether the complete module-system
  -- chain is required. A private part may borrow objects from both earlier parts.
  checkHeader path
  let base ← readModuleDataParts #[path]
  let mut parts := base
  let some first := base[0]?
    | throw <| IO.userError s!"raw.empty_parts:{name}"
  if first.1.isModule then
    for suffix in ["server", "private"] do
      let part := path.addExtension suffix
      unless ← part.pathExists do
        throw <| IO.userError s!"raw.missing_olean_part:{name}:{suffix}"
      checkHeader part
      parts := parts.push (← CompactedRegion.read (α := ModuleData) part (parts.map (·.2)))
  let some last := parts.back?
    | throw <| IO.userError s!"raw.empty_parts:{name}"
  let data := last.1
  unless data.constNames == data.constants.map (·.name) do
    throw <| IO.userError s!"raw.invalid_constant_table:{name}"
  return (data, parts.map (·.2))

unsafe def readOwn (name : Name) : IO (ModuleData × Array CompactedRegion) := do
  try readOwnParts name
  catch error => throw <| IO.userError s!"raw.read_failed:{name}:{error}"

/-- The exact compiler heads of the input-projection wire schema. An owner
cannot select the compiled-only route by supplying an empty projection. -/
def hasTypedInputs (data : ModuleData) : Bool :=
  data.constants.any Contract.SourceAudit.isInput

unsafe def loadModule (name : Name) (store : IO.Ref Store) : IO Unit := do
  let state ← store.get
  if state.modules.contains name then return
  if state.active.contains name then
    throw <| IO.userError s!"raw.import_cycle:{name}"
  store.modify fun s => { s with active := s.active.insert name }
  let (data, regions) ← readOwn name
  store.modify fun s => { s with regions := s.regions ++ regions }
  for item in data.imports do loadModule item.module store
  let mut constants ← store.modifyGet fun s => (s.constants, { s with constants := {} })
  for info in data.constants do
    if let some previous := constants[info.name]? then
      if subsumes constants info previous then constants := constants.insert info.name info
      else unless subsumes constants previous info do
        throw <| IO.userError s!"raw.conflicting_constant:{name}:{info.name}"
    else constants := constants.insert info.name info
  store.modify fun s => { s with
    constants := constants
    owners := data.constNames.foldl (fun owners constant => owners.insertIfNew constant name) s.owners
    modules := s.modules.insert name data
    moduleOrder := s.moduleOrder.push name
    metadata := CompiledMetadata.readModule s.metadata data
    active := s.active.erase name }

def Store.getModule (store : Store) (name : Name) : IO ModuleData := do
  let some data := store.modules.find? name
    | throw <| IO.userError s!"raw.missing_module:{name}"
  return data

def getConstant (find : Name → Option ConstantInfo) (name : Name) : IO ConstantInfo := do
  let some info := find name
    | throw <| IO.userError s!"raw.incomplete_closure:{name}"
  return info

end LeanInformationAudit.RawArtifacts
