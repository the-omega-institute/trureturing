import LeanInformationAudit.Contract.Decoder
import LeanInformationAudit.Contract.SourceAudit
import LeanInformationAudit.Contract.SourceLiteral

namespace LeanInformationAudit.Contract.Discovery
open Lean Meta

structure Definition where
  owner : Name
  info : DefinitionVal
  range : DeclarationRanges

structure Snapshot where
  definitions : Array Definition := #[]
  registrations : Array (Name × Decoder.CompanionInput) := #[]
  enrollments : Array (Name × TemplateEnrollmentInput) := #[]
  roots : Array (Name × RootCatalogContract) := #[]
  expected : Array (Name × LeanInformationAudit.ExpectedOccurrence) := #[]
  seals : Array (Name × SealInput) := #[]

def checkDefinition (info : ConstantInfo) : MetaM DefinitionVal := do
  if info.type.isForall then throwError "contract.discovery:forall:{info.name}"
  unless SourceAudit.heads.contains (info.type.getAppFn.constName?.getD .anonymous) do
    throwError "contract.discovery:type_alias_or_wrapper:{info.name}"
  let .defnInfo value := info | throwError "contract.discovery:not_def:{info.name}"
  unless value.safety == .safe do throwError "contract.discovery:unsafe:{info.name}"
  unless Literal.closed value.type && Literal.closed value.value do
    throwError "contract.discovery:open_term:{info.name}"
  if value.value.isLambda then throwError "contract.discovery:lambda:{info.name}"
  let head := info.type.getAppFn.constName!.str "mk"
  unless value.value.consumeMData.getAppFn.constName? == some head do
    throwError "contract.discovery:forwarding_or_computed:{info.name}"
  return value

private def candidate (env : Environment) (info : ConstantInfo)
    (unrelated : NameSet) : Bool × NameSet := Id.run do
  let (inType, unrelated) := SourceAudit.scanContract env info.type unrelated
  if inType then return (true, unrelated)
  if info.type.isSort then
    if let some value := info.value? (allowOpaque := true) then
      return SourceAudit.scanContract env value unrelated
  return (false, unrelated)

def requireRange (name : Name) : MetaM DeclarationRanges := do
  let some range ← findDeclarationRanges? name
    | throwError "contract.discovery:source_range:{name}"
  return range

/-- Source and compiled inventories must agree, including private declarations.
Rigid level parameters and their occurrences remain the compiler's original data. -/
def auditModule (owner : Name) (source : String) : MetaM (Array Definition) := do
  let env := (← getEnv).setExporting false
  let entries ← SourceAudit.parse env source owner.toString
  let map := FileMap.ofString source
  let mut found : Array Definition := #[]
  let names := if owner == env.header.mainModule then
      env.constants.map₂.toList.toArray.map Prod.fst
    else if let some idx := env.getModuleIdx? owner then
      env.header.moduleData[idx.toNat]!.constNames
    else #[]
  let constants ← names.mapM fun name => do
    let some info := env.find? name | throwError "contract.discovery:constant_missing:{name}"
    return (name, info)
  let mut unrelated : NameSet := {}
  for (name, info) in constants do
    let (relevant, cache) := candidate env info unrelated
    unrelated := cache
    unless relevant do continue
    let range ← requireRange name
    let start := map.ofPosition range.range.pos
    let stop := map.ofPosition range.range.endPos
    let some entry := entries.find? fun entry => entry.start ≤ start && stop ≤ entry.stop
      | throwError "contract.discovery:source_inventory_missing:{name}"
    let head := info.type.getAppFn.constName?.getD .anonymous
    match SourceAudit.audit entry.command head with
    | .error error => throwError "{error}:{name}"
    | .ok _ => pure ()
    match SourceLiteral.audit env (.record head) entry.command[1][3][1] name.toString with
    | .error error => throwError "{error}"
    | .ok _ => pure ()
    let value ← checkDefinition info
    unless entry.sourceName == some (privateToUserName name) do
      throwError "contract.discovery:source_name_mismatch:{name}"
    found := found.push ⟨owner, value, range⟩
  for entry in entries do
    unless entry.command.isOfKind ``Parser.Command.declaration do continue
    if SourceAudit.hasInventory entry.command then
      let mut present := entry.sourceName.any (fun sourceName =>
        names.any (fun name => privateToUserName name == sourceName))
      if entry.sourceName.isNone then
        for name in names do
          if let some range ← findDeclarationRanges? name then
            if entry.start ≤ map.ofPosition range.range.pos &&
                map.ofPosition range.range.endPos ≤ entry.stop then
              present := true
              break
      unless present do
        throwError "contract.discovery:compiled_inventory_missing:{owner}:{entry.sourceName}"
    let relevant := (entry.command.find? fun node =>
      node.isIdent && SourceAudit.heads.any (SourceAudit.isHeadSpelling node)).isSome
    unless relevant do continue
    unless found.any (fun d =>
        entry.start ≤ map.ofPosition d.range.range.pos &&
          map.ofPosition d.range.range.endPos ≤ entry.stop) do
      throwError "contract.discovery:compiled_inventory_missing:{owner}"
  return found.qsort fun a b =>
    a.range.range.pos.line < b.range.range.pos.line ||
      (a.range.range.pos.line == b.range.range.pos.line &&
        a.range.range.pos.column < b.range.range.pos.column)

def discover (moduleNames : Array Name)
    (sourceOf : Name → IO System.FilePath := ArenaProvenance.moduleSource) : MetaM Snapshot := do
  let original ← getEnv
  setEnv (original.setExporting false)
  try
    let mut result : Snapshot := {}
    let mut seen : NameSet := {}
    for owner in moduleNames do
      if seen.contains owner then throwError "contract.discovery:duplicate_module:{owner}"
      seen := seen.insert owner
      unless owner == original.header.mainModule || (original.getModuleIdx? owner).isSome do
        throwError "contract.discovery:module_missing:{owner}"
      let source ← IO.FS.readFile (← sourceOf owner)
      let definitions ← auditModule owner source
      for definition in definitions do
        let info := definition.info
        let head := info.type.getAppFn.constName!
        if head == ``Contract.Registration then
          result := { result with registrations := result.registrations.push (owner, ← Decoder.registration owner info source) }
        else if head == ``Contract.TemplateEnrollment then
          result := { result with enrollments := result.enrollments.push (owner, ← Decoder.enrollment owner info source) }
        else if head == ``Contract.RootCatalog then
          result := { result with roots := result.roots.push (owner, ← Decoder.rootCatalog info.value) }
        else if head == ``Contract.ExpectedDeclaration then
          result := { result with expected := result.expected.push (owner, ← Decoder.expectedDeclaration info.value) }
        else if head == ``Contract.Seal then
          result := { result with seals := result.seals.push (owner, ← Decoder.readSeal info.value) }
      result := { result with definitions := result.definitions ++ definitions }
    return result
  finally setEnv original

end LeanInformationAudit.Contract.Discovery
