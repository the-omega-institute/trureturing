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
  if info.isCtor || info.isTheorem || isAuxRecursor env info.name ||
      isNoConfusion env info.name || (env.getProjectionFnInfo? info.name).isSome then
    return (false, unrelated)
  if info.name == info.name.getPrefix.str "_flat_ctor" then
    if let some (.ctorInfo _) := env.find? info.name.getPrefix then return (false, unrelated)
  let (inType, unrelated) := SourceAudit.scanContract env (SourceAudit.resultType info.type) unrelated
  if inType then return (true, unrelated)
  if info.type.isSort then
    if let some value := info.value? (allowOpaque := true) then
      return SourceAudit.scanContract env value unrelated
  return (false, unrelated)

def requireRange (name : Name) : MetaM DeclarationRanges := do
  let some range ← findDeclarationRanges? name
    | throwError "contract.discovery:source_range:{name}"
  return range

def moduleSource (name : Name) : IO System.FilePath := do
  if Repository.isImplementationSourceModule name then
    Repository.source ("tools/lean-inspector/" ++ name.toString.replace "." "/" ++ ".lean")
  else ArenaProvenance.moduleSource name

/-- The existing arena marker delegates syntax unchanged to a core structure
elaborator. It only annotates mathematical arena expressions; contract metadata
is assembled by the core delegate. This permission names its compiler owner,
private-aware identity and exact direct delegation shape. -/
private def coreStructureDelegate (env : Environment) (name : Name) : Bool := Id.run do
  let some idx := env.getModuleIdxFor? name | return false
  unless env.header.moduleNames[idx.toNat]! == `LeanInformationAuditInterface.Syntax do
    return false
  unless #[`LeanInformationAudit.elabArenaConstruction,
      `LeanInformationAudit.elabDefaultArenaConstruction].contains (privateToUserName name) do
    return false
  let some info := env.find? name | return false
  let some body := info.value? (allowOpaque := true) | return false
  let some marker := body.getAppFn.constName? | return false
  unless privateToUserName marker == `LeanInformationAudit.markArenaConstruction &&
      env.getModuleIdxFor? marker == some idx && body.getAppArgs.size == 1 do return false
  let some markerInfo := env.find? marker | return false
  let some markerBody := markerInfo.value? (allowOpaque := true) | return false
  unless Sha256.hex (reprStr markerBody).toUTF8 ==
      "13a94365395add495532e09e0c8968203c92a091e569a11a3e26fb059e84a2b1" do return false
  return #[`Lean.Elab.Term.StructInst.elabStructInst,
    `Lean.Elab.Term.StructInst.elabStructInstDefault].any (body.getAppArgs[0]!.isConstOf ·)

/-- Audit the compiler import DAG, restricted to source files inside this
checkout. Core Lean and pinned external libraries supply the permitted builtin
syntax. Missing repository sources are errors, never silently skipped. -/
def importExpansionKeys (owner : Name) (sourceOf : Name → IO System.FilePath)
    : MetaM NameSet := do
  let env ← getEnv
  let root ← Repository.root
  let mut pending := #[owner]
  let mut seen : NameSet := {}
  let mut keys : NameSet := {}
  while !pending.isEmpty do
    let moduleName := pending.back!
    pending := pending.pop
    if seen.contains moduleName then continue
    seen := seen.insert moduleName
    if let some idx := env.getModuleIdx? moduleName then
      pending := pending ++ env.header.moduleData[idx.toNat]!.imports.map (·.module)
    else if moduleName == env.header.mainModule then
      pending := pending ++ env.header.imports.map (·.module)
    let path ← if moduleName == owner then sourceOf moduleName
      else pure (root / LeanInformationAudit.TemplateAudit.sourcePath moduleName)
    unless ← path.pathExists do
      if Repository.isModule moduleName || Repository.isImplementationSourceModule moduleName then
        throwError "contract.source_literal:source_missing:{moduleName}"
      continue
    let path ← IO.FS.realPath path
    unless moduleName == owner ||
        ((root.toString ++ "/").isPrefixOf path.toString &&
          !((root / ".lake").toString ++ "/").isPrefixOf path.toString) do continue
    let entries ← SourceAudit.parse env (← IO.FS.readFile path) moduleName.toString
    let mut delegates : NameSet := {}
    if let some idx := env.getModuleIdx? moduleName then
      for name in env.header.moduleData[idx.toNat]!.constNames do
        if coreStructureDelegate env name then delegates := delegates.insert (privateToUserName name)
    for key in (SourceAudit.expansionKeys entries delegates).toArray do keys := keys.insert key
    if let some idx := env.getModuleIdx? moduleName then
      for entry in Elab.macroAttribute.ext.ext.getModuleEntries env idx do
        let value := match entry with | .global e | .scoped _ e => e
        keys := keys.insert value.key
      for entry in Elab.Term.termElabAttribute.ext.ext.getModuleEntries env idx do
        let value := match entry with | .global e | .scoped _ e => e
        unless coreStructureDelegate env value.declName do keys := keys.insert value.key
  return keys

/-- Source and compiled inventories must agree, including private declarations.
Rigid level parameters and their occurrences remain the compiler's original data. -/
def auditModule (owner : Name) (source : String) : MetaM (Array Definition) := do
  let env := (← getEnv).setExporting false
  let entries ← SourceAudit.parse env source owner.toString
  let map := FileMap.ofString source
  let mut found : Array Definition := #[]
  let mut expansionKeys : Option NameSet := none
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
    let head := (SourceAudit.resultType info.type).getAppFn.constName?.getD .anonymous
    let functionDefinition := match info with
      | .defnInfo _ => info.type.isForall
      | _ => false
    unless SourceAudit.heads.contains head || functionDefinition do
      throwError "contract.discovery:type_alias_or_wrapper:{name}"
    let range ← requireRange name
    let start := map.ofPosition range.range.pos
    let stop := map.ofPosition range.range.endPos
    let some entry := entries.find? fun entry => entry.start ≤ start && stop ≤ entry.stop
      | throwError "contract.discovery:source_inventory_missing:{name}"
    match SourceAudit.audit entry.command head with
    | .error error => throwError "{error}:{name}"
    | .ok _ => pure ()
    if info.type.isForall && SourceAudit.heads.contains head then
      throwError "contract.discovery:term_parameters:{name}"
    if expansionKeys.isNone then
      expansionKeys := some (← importExpansionKeys owner fun _ => do
        return ← moduleSource owner)
    match SourceLiteral.audit env (.record head) entry.command[1][3][1] name.toString (expansionKeys.getD {}) with
    | .error error => throwError "{error}"
    | .ok _ => pure ()
    let value ← checkDefinition info
    unless entry.sourceName == some (privateToUserName name) do
      throwError "contract.discovery:source_name_mismatch:{name}"
    found := found.push ⟨owner, value, range⟩
  for entry in entries do
    unless entry.command.isOfKind ``Parser.Command.declaration do continue
    if SourceAudit.hasInventory entry.command then
      let mut present := false
      for name in names do
        unless entry.sourceName.isNone ||
            entry.sourceName == some (privateToUserName name) do continue
        if let some range ← findDeclarationRanges? name then
          if entry.start ≤ map.ofPosition range.range.pos &&
              map.ofPosition range.range.endPos ≤ entry.stop then
            present := true
            break
      unless present do
        throwError "contract.discovery:compiled_inventory_missing:{owner}:{entry.sourceName}"
  return found.qsort fun a b =>
    a.range.range.pos.line < b.range.range.pos.line ||
      (a.range.range.pos.line == b.range.range.pos.line &&
        a.range.range.pos.column < b.range.range.pos.column)


def discover (moduleNames : Array Name)
    (sourceOf : Name → IO System.FilePath := moduleSource) : MetaM Snapshot := do
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
