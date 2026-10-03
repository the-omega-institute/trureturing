import LeanInformationAudit.Contract.Decoder
import LeanInformationAudit.Contract.SourceAudit
import LeanInformationAudit.Contract.SourceLiteral
import LeanInformationAudit.Contract.RootStructure

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
      for entry in Elab.Tactic.tacticElabAttribute.ext.ext.getModuleEntries env idx do
        let value := match entry with | .global e | .scoped _ e => e
        keys := keys.insert value.key
      for entry in Elab.Command.commandElabAttribute.ext.ext.getModuleEntries env idx do
        let value := match entry with | .global e | .scoped _ e => e
        keys := keys.insert value.key
  return keys

/-- Exact nonrecursive equation suffixes emitted for literal entries by the
pinned compiler. No numbered family, matcher, where or let-rec prefix is allowed. -/
def entryEquationSuffixes : Array String := #["eq_1", "eq_def"]

/-- Equation permission requires the compiler reserved identity, a theorem with
its simple reflexive equation shape, no authored ownership or elaboration, and
same-module ownership. Every other compiled constant is audited normally. -/
def generatedEntryAuxiliary (owner : Name) (entries : Array SourceAudit.Entry)
    (definitions : Array Definition) (env : Environment) (name : Name)
    (forbidden : NameSet := {}) : MetaM Bool := do
  if entries.any (fun entry => entry.authoredNames.contains (privateToUserName name)) then
    return false
  let belongs := if owner == env.header.mainModule then env.getModuleIdxFor? name == none
    else env.getModuleIdxFor? name == env.getModuleIdx? owner
  unless belongs do return false
  let some (.thmInfo info) := env.find? name | return false
  let .str _ suffix := name | return false
  unless entryEquationSuffixes.contains suffix do return false
  for definition in definitions do
    let parent := privateToUserName definition.info.name
    let child := privateToUserName name
    let some entry := entries.find? (·.sourceName == some parent) | continue
    if SourceAudit.entryHasAuthoredElaboration entry forbidden then continue
    unless name == Meta.mkEqLikeNameFor env definition.info.name suffix &&
        isReservedName env name do continue
    if entries.any (fun entry => entry.authoredNames.any fun authored =>
        authored != parent && authored.isPrefixOf child) then continue
    unless info.type.isAppOfArity ``Eq 3 &&
        info.type.getAppArgs[1]!.isConstOf definition.info.name &&
        info.type.getAppArgs[2]!.consumeMData == definition.info.value.consumeMData &&
        info.value.isAppOfArity ``Eq.refl 2 &&
        info.value.getAppArgs[1]!.isConstOf definition.info.name do continue
    if let some range ← findDeclarationRanges? name then
      let outer := definition.range.range
      let inner := range.range
      unless (outer.pos.line < inner.pos.line ||
          (outer.pos.line == inner.pos.line && outer.pos.column ≤ inner.pos.column)) &&
          (inner.endPos.line < outer.endPos.line ||
          (inner.endPos.line == outer.endPos.line && inner.endPos.column ≤ outer.endPos.column)) do
        continue
    return true
  return false

/-- Source and compiled inventories must agree, including private declarations.
Rigid level parameters and their occurrences remain the compiler's original data. -/
def auditModule (owner : Name) (source : String) : MetaM (Array Definition) := do
  let env := (← getEnv).setExporting false
  let entries ← SourceAudit.parse env source owner.toString
  if (`Reg).isPrefixOf owner then
    match SourceAudit.auditRegCommands owner entries with
    | .error error => throwError error
    | .ok _ => pure ()
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
  for (name, info) in constants do
    let head := info.type.getAppFn.constName?.getD .anonymous
    unless SourceAudit.heads.contains head do continue
    -- A generated auxiliary is not an authored entry, even if it has a head.
    unless entries.any (fun entry => entry.sourceName == some (privateToUserName name)) do
      continue
    let range ← requireRange name
    let start := map.ofPosition range.range.pos
    let stop := map.ofPosition range.range.endPos
    let some entry := entries.find? fun entry => entry.start ≤ start && stop ≤ entry.stop
      | throwError "contract.discovery:source_inventory_missing:{name}"
    if entry.command[1].isOfKind ``Parser.Command.definition then
      unless SourceAudit.isHeadSpelling
          (SourceAudit.termHead entry.command[1][2][1][0][1]) head do continue
    match SourceAudit.audit entry.command head with
    | .error error => throwError "{error}:{name}"
    | .ok _ => pure ()
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
  for (name, info) in constants do
    if found.any (fun definition => definition.info.name == name) then continue
    if ← generatedEntryAuxiliary owner entries found env name (expansionKeys.getD {}) then continue
    let references := SourceAudit.directInterfaceReferences env info
    unless references.isEmpty do
      throwError "contract.reg:contract_reference_outside_entry:{name}:{references}"
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


def discoverWithStructure (requirements : Array RootStructure.Requirement)
    (moduleNames : Array Name)
    (sourceOf : Name → IO System.FilePath := moduleSource) : MetaM Snapshot := do
  let original ← getEnv
  setEnv (original.setExporting false)
  try
    RootStructure.checkScope requirements moduleNames
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
          throwError "contract.root_structure:independent_expected_not_allowed:{owner}:{info.name}"
        else if head == ``Contract.Seal then
          result := { result with seals := result.seals.push (owner, ← Decoder.readSeal info.value) }
      result := { result with definitions := result.definitions ++ definitions }
    RootStructure.check requirements moduleNames result.roots result.seals
    return result
  finally setEnv original

/-- Production constructs obligations from the Reg source-tree path rule before
discovery. Isolated tests can supply requirements from their own source tree;
no decoded contract entry determines its module kind. -/
def discover (moduleNames : Array Name)
    (sourceOf : Name → IO System.FilePath := moduleSource) : MetaM Snapshot := do
  let env ← getEnv
  let requirements ← RootStructure.required env
  for owner in env.header.moduleNames.push env.header.mainModule do
    if (`Reg).isPrefixOf owner && !moduleNames.contains owner then
      throwError "contract.root_structure:required_module_missing:{owner}"
  discoverWithStructure requirements moduleNames sourceOf

end LeanInformationAudit.Contract.Discovery
