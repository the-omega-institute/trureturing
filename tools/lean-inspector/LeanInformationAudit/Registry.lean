import LeanInformationAudit.Registry.Assessment

namespace LeanInformationAudit.TemplateBinding
open Lean Meta TemplateAudit

private initialize familyRegistrations : SimplePersistentEnvExtension TemplateOccurrenceKey (Array TemplateOccurrenceKey) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push, addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }

def familyKeys (env : Environment) : Array TemplateOccurrenceKey := familyRegistrations.getState env

private initialize occurrenceInventory : SimplePersistentEnvExtension TemplateOccurrenceEvent (Array TemplateOccurrenceEvent) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }
private initialize bindingRecords : SimplePersistentEnvExtension BindingRecord (Array BindingRecord) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }
private initialize bindingClaims : SimplePersistentEnvExtension TemplateBindingClaim (Array TemplateBindingClaim) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }

structure ResolvedDeclaration where
  theoremName : Name
  arena : Name
  descriptor : Option Expr
  diagnostic : Option String := none
  escapeInput : EscapeRecordInput := {}

private initialize pendingDeclaration : EnvExtension (Option ResolvedDeclaration) ←
  registerEnvExtension (pure none)

/-- Scoped syntax input, never enrollment or certification authority. The
registration transaction owns rollback; the inner scope always clears itself. -/
private def eraseDescriptor (descriptor : Option Expr) (diagnostic : Option String) :
    Elab.Command.CommandElabM (Option Expr × Option String) := Elab.Command.liftTermElabM do
  try
    let descriptor ← descriptor.mapM fun value => do
      return (← TemplateAudit.withCumulativeBudget <| TemplateAudit.eraseProofs value
        (TemplateAudit.informationTemplate.work.get (← getOptions))).1
    return (descriptor, diagnostic)
  catch error =>
    return (none, some ("incomplete_closure:E8.descriptor_erasure:" ++
      (← error.toMessageData.toString)))

def withDeclaration (declaration : ResolvedDeclaration)
    (action : Elab.Command.CommandElabM Unit) : Elab.Command.CommandElabM Unit := do
  let (descriptor, diagnostic) ← eraseDescriptor declaration.descriptor declaration.diagnostic
  let declaration := { declaration with descriptor, diagnostic }
  let previous := pendingDeclaration.getState (← getEnv)
  if previous.isSome then throwError "unclassified_form:dtr.nested_declaration"
  modifyEnv (pendingDeclaration.setState · (some declaration))
  try action
  finally modifyEnv (pendingDeclaration.setState · previous)

def inventory (env : Environment) : Array TemplateOccurrenceEvent := occurrenceInventory.getState env
def records (env : Environment) : Array BindingRecord := bindingRecords.getState env

/-- Origin labels come from the native extension container, separately from
the owner asserted in a claim. Local claims have the current module as origin. -/
private def ownedClaims (env : Environment) : Array (Name × TemplateBindingClaim) := Id.run do
  let mut result := #[]
  for index in [:env.header.moduleNames.size] do
    let owner := env.header.moduleNames[index]!
    for claim in bindingClaims.getModuleEntries env index do
      result := result.push (owner, claim)
  for claim in bindingClaims.getEntries env do
    result := result.push (env.header.mainModule, claim)
  return result

private def ownedEvents (env : Environment) : Array (Name × TemplateOccurrenceEvent) := Id.run do
  let mut result := #[]
  for index in [:env.header.moduleNames.size] do
    let owner := env.header.moduleNames[index]!
    for event in occurrenceInventory.getModuleEntries env index do
      result := result.push (owner, event)
  for event in (occurrenceInventory.getEntries env).reverse do
    result := result.push (env.header.mainModule, event)
  return result

/-- Pure join validation grants no insertion or certification capability.
Both publication and authoritative assessment consume this same relation. -/
def joinClaims (events : Array (Name × TemplateOccurrenceEvent))
    (claims : Array (Name × TemplateBindingClaim)) :
    Except String (Array (TemplateOccurrenceEvent × Option TemplateBindingClaim)) := do
  let mut indexed : Std.HashMap TemplateOccurrenceKey TemplateOccurrenceEvent := {}
  for (producer, event) in events do
    unless producer == event.key.registrationModule do throw "incomplete_closure:dtr.event_owner"
    if indexed.contains event.key then throw "incomplete_closure:dtr.duplicate_occurrence"
    indexed := indexed.insert event.key event
  let mut selected : Std.HashMap TemplateOccurrenceKey TemplateBindingClaim := {}
  for (producer, claim) in claims do
    unless producer == claim.owner do throw "incomplete_closure:dtr.claim_owner"
    unless indexed.contains claim.key do throw "unclassified_form:dtr.dangling_claim"
    if selected.contains claim.key then throw "unclassified_form:dtr.duplicate_claim"
    if let some event := indexed[claim.key]? then
      unless claim.arena.equal event.arena do throw "unclassified_form:dtr.claim_occurrence"
    selected := selected.insert claim.key claim
  return events.map fun (_, event) => (event, selected[event.key]?)

/-- Reuse producer-issued results for mathematical publication in this immutable
environment. This join issues no certificate and makes no claim about subsequent
filesystem changes. The authoritative report rechecks source inputs and assesses
the full join through `assessJoined` before admission can consume its evidence. -/
def cachedJoinedRecords (env : Environment) : Except String (Array BindingRecord) := do
  let joined ← joinClaims (ownedEvents env) (ownedClaims env)
  let retained := records env
  for index in [:env.header.moduleNames.size] do
    let owner := env.header.moduleNames[index]!
    for record in bindingRecords.getModuleEntries env index do
      unless record.bindingOwner.getD record.occurrence.key.registrationModule == owner do
        throw "incomplete_closure:dtr.cached_record_owner"
  joined.mapM fun (event, claim) => do
    let owner := claim.map (·.owner)
    let candidates := retained.filter fun record =>
      record.occurrence.key == event.key && record.bindingOwner == owner
    unless candidates.size == 1 do throw "incomplete_closure:dtr.cached_record_missing"
    let record := candidates[0]!
    let occurrence := record.occurrence
    unless occurrence.statementIdentity == event.statementIdentity &&
        occurrence.statement.equal event.statement && occurrence.levelParams == event.levelParams &&
        occurrence.arena.equal event.arena && occurrence.unitName == event.unitName &&
        occurrence.realizationName == event.realizationName &&
        occurrence.registrationSource == event.registrationSource &&
        occurrence.registrationSourceIdentity == event.registrationSourceIdentity &&
        occurrence.familyScope == event.familyScope do
      throw "incomplete_closure:dtr.cached_record_inputs"
    match claim, record.descriptor with
    | none, none =>
      unless record.result matches .undeclared do
        throw "incomplete_closure:dtr.cached_undeclared"
    | some claim, descriptor =>
      unless claim.arena.equal event.arena && (match claim.descriptor, descriptor with
        | none, none => true
        | some a, some b => a.equal b
        | _, _ => false) do
        throw "incomplete_closure:dtr.cached_descriptor"
      if let .declaredValidated certificate := record.result then
        unless certificate.key == event.key && claim.resolutionDiagnostic.isNone && descriptor.isSome do
          throw "incomplete_closure:dtr.cached_certificate"
      if record.result matches .undeclared then
        throw "incomplete_closure:dtr.cached_declared"
    | _, _ => throw "incomplete_closure:dtr.cached_descriptor"
    return record

def sourcePath := TemplateAudit.sourcePath

def publishRegistration (entry : InformationRegistryEntry) : Elab.Command.CommandElabM Unit := do
  let info ← getConstInfo entry.theoremName
  let statementIdentity := match TemplateAudit.rawStatementIdentity info.levelParams info.type with
    | .ok (identity, _) => identity
    | .error _ => ""
  let path := sourcePath entry.registrationModuleName
  let sourceIdentity ← try pure (Sha256.hex (← IO.FS.readBinFile path)) catch _ => pure ""
  let event : TemplateOccurrenceEvent := {
    key := {
      root := entry.registrationModuleName
      registrationModule := entry.registrationModuleName
      theoremName := entry.theoremName
      objectArena := entry.canonicalObjectArenaName
      catalog := entry.effectiveCatalogId }

    unitName := entry.unitName, realizationName := entry.realizationName,
    statement := info.type, levelParams := info.levelParams, statementIdentity,
    arena := mkConst entry.canonicalObjectArenaName,
    registrationSource := path, registrationSourceIdentity := sourceIdentity }
  let claim ← match pendingDeclaration.getState (← getEnv) with
    | none => pure none
    | some declaration =>
      unless declaration.theoremName == event.key.theoremName && declaration.arena == event.key.objectArena do
        throwError "unclassified_form:dtr.inline_occurrence"
      pure <| some {
        key := event.key, arena := event.arena, descriptor := declaration.descriptor,
        resolutionDiagnostic := declaration.diagnostic, escapeInput := declaration.escapeInput, owner := (← getEnv).header.mainModule : TemplateBindingClaim }
  let record ← Elab.Command.liftTermElabM <| assess event claim
  modifyEnv fun current => bindingRecords.addEntry (occurrenceInventory.addEntry current event) record
  if let some claim := claim then modifyEnv (bindingClaims.addEntry · claim)
  if record.result matches .undeclared then logWarning (missingDeclarationDiagnostic event.key)
  if let .declaredUnresolved diagnostic := record.result then logWarning diagnostic

/-- Explicit family registration, including registrations in source sidecars.
The typed record remains separate from all finite theorem-unit/catalog registries. -/
def publishFamily (theoremName arenaName recordName : Name) (selection : FamilySourceSelection)
    (descriptor : Option Expr) (diagnostic : Option String) : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  let info ← getConstInfo theoremName
  let owner := env.header.mainModule
  let (scope, _) ← Elab.Command.liftTermElabM <| FamilySource.resolve info selection
  let .ok (statementIdentity, _) := TemplateAudit.rawStatementIdentity info.levelParams info.type
    | throwError "incomplete_closure:family.source.identity"
  let path := sourcePath owner
  let input ← Elab.Command.liftCoreM <| TemplateAudit.readSourceInput path
  let event : TemplateOccurrenceEvent := {
    key := {
      mode := .dependentFamily, root := owner, registrationModule := owner, theoremName, objectArena := arenaName, catalog := arenaName }
    unitName := recordName, realizationName := recordName,
    statement := info.type, levelParams := info.levelParams, statementIdentity,
    arena := mkConst arenaName (info.levelParams.map Level.param),
    registrationSource := path, registrationSourceIdentity := input.sha256,
    familyScope := some scope }
  if (inventory env).any (·.key == event.key) then
    throwError "unclassified_form:dtr.duplicate_occurrence"
  let (descriptor, diagnostic) ← eraseDescriptor descriptor diagnostic
  let claim : TemplateBindingClaim := {
    key := event.key, arena := event.arena, descriptor, resolutionDiagnostic := diagnostic,
    escapeInput := { openContinuation := true }, owner }
  let result ← Elab.Command.liftTermElabM <| assess event (some claim)
  modifyEnv fun current => familyRegistrations.addEntry
    (bindingRecords.addEntry (bindingClaims.addEntry
      (occurrenceInventory.addEntry current event) claim) result) event.key
  if let .declaredUnresolved diagnostic := result.result then logWarning diagnostic

/-- Claims join by their exact occurrence identity before authoritative assessment.
An overlay retains the original registration owner and cannot replace an inline claim. -/
def declareSidecar (theoremName arena : Name) (catalog : Option Name)
    (descriptor : Option Expr) (resolutionDiagnostic : Option String)
    (escapeInput : EscapeRecordInput := {}) : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  let matching := (inventory env).filter fun event => event.key.theoremName == theoremName &&
    event.key.objectArena == arena && (catalog.isNone || catalog == some event.key.catalog)
  unless matching.size == 1 do throwError "unclassified_form:dtr.sidecar_occurrence"
  let event := matching[0]!
  if (bindingClaims.getState env).any (·.key == event.key) then
    throwError "unclassified_form:dtr.duplicate_claim"
  let (descriptor, resolutionDiagnostic) ← eraseDescriptor descriptor resolutionDiagnostic
  let claim : TemplateBindingClaim := {
    key := event.key, arena := event.arena, descriptor, resolutionDiagnostic, escapeInput,
    owner := env.header.mainModule }
  let record ← Elab.Command.liftTermElabM <| assess event (some claim)
  modifyEnv fun current => bindingRecords.addEntry (bindingClaims.addEntry current claim) record
  if let .declaredUnresolved diagnostic := record.result then logWarning diagnostic

/-- A realization provider may be imported by its registration source. The
complete report environment can contain other, unrelated owners as well. -/
private def ownerReachable (env : Environment) (root owner : Name) : Bool := Id.run do
  let mut seen : NameSet := {}
  let mut pending := [root]
  while let name :: rest := pending do
    pending := rest
    if seen.contains name then continue
    if name == owner then return true
    seen := seen.insert name
    let imports := if name == env.header.mainModule then env.header.imports else
      match env.getModuleIdx? name with
      | some index => env.header.moduleData[index.toNat]!.imports
      | none => #[]
    pending := imports.toList.map (·.module) ++ pending
  return false

/-- A replayed event cannot acquire current source or statement identities by
being exported from a new root. Check the original owner and retained bytes. -/
def validateEvent (event : TemplateOccurrenceEvent) : MetaM Unit := do
  let env ← getEnv
  unless event.registrationSource == sourcePath event.key.registrationModule &&
      event.key.root == event.key.registrationModule do
    throwError "incomplete_closure:dtr.event_owner"
  let input ← TemplateAudit.readSourceInput event.registrationSource
  unless input.sha256 == event.registrationSourceIdentity do
    throwError "incomplete_closure:dtr.event_source"
  let info ← getConstInfo event.key.theoremName
  let .ok (identity, _) := TemplateAudit.rawStatementIdentity info.levelParams info.type
    | throwError "incomplete_closure:dtr.event_statement"
  unless identity == event.statementIdentity && info.levelParams == event.levelParams &&
      info.type.equal event.statement do
    throwError "incomplete_closure:dtr.event_statement"
  let unitOwner := (RegistrationReifier.declaringModuleOf env event.unitName).getD env.header.mainModule
  unless env.contains event.unitName && (if event.key.mode == .dependentFamily then
      ownerReachable env event.key.registrationModule unitOwner else
      unitOwner == event.key.registrationModule) do
    throwError "incomplete_closure:dtr.event_unit_owner"
  let realizationOwner := (RegistrationReifier.declaringModuleOf env event.realizationName).getD
    env.header.mainModule
  unless env.contains event.realizationName &&
      ownerReachable env event.key.registrationModule realizationOwner do
    throwError "incomplete_closure:dtr.event_unit_owner"

/-- Snapshot for the complete imported join. Original provisional records are
retained only for transport to the C# join; selected contains one final result. -/
structure JoinedRecords where
  selected : Array BindingRecord
  originals : Array BindingRecord

/-- Shared final assessment after the full imported claim set has been joined.
Callers must establish complete governed sidecar inputs before claiming coverage. -/
def assessJoined : MetaM (Array BindingRecord) := do
  let env ← getEnv
  let joined ← match joinClaims (ownedEvents env) (ownedClaims env) with
    | .ok joined => pure joined
    | .error reason => throwError reason
  for (event, _) in joined do validateEvent event
  joined.mapM fun (event, claim) => assess event claim

/-- Export always starts by joining the entire loaded declaration universe. -/
def exportSnapshot : MetaM JoinedRecords := do
  -- Empty inventories still execute this judge. Validate its compiled source
  -- before collecting records or binding current source hashes to the export.
  TemplateAudit.NativeCoherence.validate #[`LeanInformationAudit.Registry]
  let selected ← assessJoined
  let originals ← (inventory (← getEnv)).mapM fun event => do
    let some original := (records (← getEnv)).find? (·.occurrence.key == event.key)
      | throwError "incomplete_closure:dtr.original_inventory"
    return original
  return { selected, originals }

def keyJson (key : TemplateOccurrenceKey) : Json := Json.mkObj [
  ("mode", toJson key.mode.wireName),
  ("root", toJson key.root.toString), ("registration_module", toJson key.registrationModule.toString),
  ("theorem", toJson key.theoremName.toString), ("object_arena", toJson key.objectArena.toString),
  ("catalog", toJson key.catalog.toString)]

private def certificateJson (certificate : TemplateBindingCertificate) : Json := Json.mkObj [
  ("key", keyJson certificate.key), ("evidence_ref", toJson certificate.evidenceRef),
  ("plan_identity", toJson certificate.planIdentity),
  ("descriptor_identity", toJson certificate.descriptorIdentity),
  ("actual_identity", toJson certificate.actualIdentity),
  ("argument_inputs", Json.arr (certificate.argumentInputs.map dependencyJson)),
  ("extraction_inputs", Json.arr (certificate.extractionInputs.map dependencyJson))]

private def isRepositoryModule (name : Name) : Bool :=
  name.toString.startsWith "D5." || name.toString.startsWith "LeanInformationAudit." ||
    name == `Trureturing

private def isRecordedModule (name : Name) : Bool :=
  name.toString.startsWith "D5." || name.toString.startsWith "LeanInformationAudit.Tests." ||
    name == `Trureturing

private def moduleSourceInputs (env : Environment) (root : Name) :
    CoreM (Array TemplateAudit.SourceInput × Nat) := do
  let mut seen : NameSet := {}
  let mut pending := [root]
  let mut paths := TemplateAudit.policyPaths
  while let name :: rest := pending do
    pending := rest
    if seen.contains name then continue
    seen := seen.insert name
    unless isRepositoryModule name do continue
    if isRecordedModule name then
      let path := sourcePath name
      unless paths.contains path do paths := paths.push path
    let imports ← if name == env.header.mainModule then pure env.header.imports
      else if let some index := env.getModuleIdx? name then
        pure env.header.moduleData[index.toNat]!.imports
      else throwError "incomplete_closure:dtr.module_imports:{name}"
    pending := imports.toList.map (·.module) ++ pending
  TemplateAudit.readVersionedSourceInputs (paths.qsort (· < ·))

/-- Complete source inputs for an independently requested module. Batch reports
use the same source walk inside their union's native-validation boundaries. -/
def moduleInputs (env : Environment) (root : Name) : CoreM (Array TemplateAudit.SourceInput) := do
  TemplateAudit.NativeCoherence.validate (#[root] ++
    (if root == env.header.mainModule then env.header.imports.map (·.module) else #[]))
  return (← moduleSourceInputs env root).1

/-- Content touches follow actual constant dependencies, including complete
arena/realization types, while theorem proof implementations are never entered. -/
private def contentInputs (record : BindingRecord) : MetaM (Array TemplateAudit.SourceInput) := do
  let env ← getEnv
  let mut pending := [record.occurrence.key.theoremName, record.occurrence.unitName,
    record.occurrence.realizationName, record.occurrence.key.objectArena]
  if let some origin := record.escape.fromObject then pending := origin.name :: pending
  if let some residual := record.escape.continuation then
    pending := residual.declarationName.toList ++ residual.chainName.toList ++ pending
  if let some descriptor := record.descriptor then
    let erased ← TemplateAudit.eraseProofs descriptor
    pending := (erased.1.getUsedConstants.filter (· != ``lcProof)).toList ++ pending
  let mut seen : NameSet := {}
  let mut paths := #[record.occurrence.registrationSource]
  if let some owner := record.bindingOwner then paths := paths.push (sourcePath owner)
  let mut remaining := 524288
  while let name :: rest := pending do
    pending := rest
    if seen.contains name then continue
    if remaining == 0 then throwError "incomplete_closure:dtr.content_inputs"
    remaining := remaining - 1
    seen := seen.insert name
    let info ← getConstInfo name
    let owner := (RegistrationReifier.declaringModuleOf env name).getD env.header.mainModule
    -- The family content slice ends at native-validated judge/toolchain/package
    -- owners. Those immutable inputs have their separate version/pin closure;
    -- following their implementations cannot discover later content modules.
    if record.occurrence.key.mode == .dependentFamily && !isRecordedModule owner then continue
    if isRepositoryModule owner then
      let path := sourcePath owner
      unless paths.contains path ||
          (record.occurrence.key.mode == .fixedState && path.startsWith "tools/") do paths := paths.push path
    let (type, work) ← TemplateAudit.eraseProofs info.type remaining
    remaining := remaining - work
    pending := (type.getUsedConstants.filter (· != ``lcProof)).toList ++ pending
    if !info.isTheorem then
      if let some value := info.value? then
        let (value, work) ← TemplateAudit.eraseProofs value remaining
        remaining := remaining - work
        pending := (value.getUsedConstants.filter (· != ``lcProof)).toList ++ pending
  (paths.toList.eraseDups.toArray.qsort (· < ·)).mapM fun path => TemplateAudit.readSourceInput path

private def inputJson (input : TemplateAudit.SourceInput) : Json := Json.mkObj [
  ("path", toJson input.path), ("sha256", toJson input.sha256)]

private def escapeFromJson (origin : EscapeFromIdentity) : Json := Json.mkObj [
  ("name", toJson origin.name.toString), ("type_identity", toJson origin.typeIdentity),
  ("object_identity", toJson origin.objectIdentity)]

private def escapeContinuationJson (residual : EscapeContinuationIdentity) : Json := Json.mkObj [
  ("kind", toJson residual.kind),
  ("declaration_name", toJson (residual.declarationName.map Name.toString)),
  ("statement_identity", toJson residual.statementIdentity),
  ("chain_name", toJson (residual.chainName.map Name.toString))]

/-- Shared record wire for the inspector and census authoritative snapshots. -/
def recordJson (record : BindingRecord) : MetaM Json := do
  let (state, diagnostic, certificate) := match record.result with
    | .undeclared => ("undeclared", toJson (missingDeclarationDiagnostic record.occurrence.key), Json.null)
    | .declaredUnresolved diagnostic => ("declared_unresolved", toJson diagnostic, Json.null)
    | .declaredValidated certificate => ("declared_validated", Json.null, certificateJson certificate)
  let base := [
    ("key", keyJson record.occurrence.key),
    ("registration_source_path", toJson record.occurrence.registrationSource),
    ("statement_identity", toJson record.occurrence.statementIdentity),
    ("unit_name", toJson record.occurrence.unitName.toString),
    ("realization_name", toJson record.occurrence.realizationName.toString),
    ("escape_from", if record.occurrence.key.mode == .dependentFamily then
      record.escape.family.map (fun evidence => Json.mkObj [
        ("kind", toJson "source-occurrence"), ("source", toJson record.occurrence.key.theoremName.toString),
        ("scope_identity", toJson evidence.identity)]) |>.getD Json.null
      else record.escape.fromObject.map escapeFromJson |>.getD Json.null),
    ("escape_continues", record.escape.continuation.map escapeContinuationJson |>.getD Json.null),
    ("bridge_kind", toJson record.escape.bridgeKind),
    ("content_inputs", Json.arr ((← contentInputs record).map inputJson)),
    ("binding_source_path", record.bindingOwner.map (toJson ∘ sourcePath) |>.getD Json.null),
    ("state", toJson state), ("diagnostic", diagnostic), ("certificate", certificate)]
  return Json.mkObj (base ++ if record.occurrence.key.mode == .dependentFamily then
    [("family_binding", record.escape.family.map (fun evidence => Json.mkObj [
      ("identity", toJson evidence.identity), ("material", evidence.material)]) |>.getD Json.null)]
    else [])

/-- Records are partitioned by their actual producing module. An original
undeclared row and a sidecar overlay remain distinguishable until the final join. -/
private def moduleJson (snapshot : JoinedRecords) (moduleName : Name)
    (registered : Array TemplateOccurrenceKey) : MetaM Json := do
  let env ← getEnv
  let originals := snapshot.originals.filter (·.occurrence.key.registrationModule == moduleName)
  let overlays := snapshot.selected.filter fun row => row.bindingOwner == some moduleName &&
    row.occurrence.key.registrationModule != moduleName
  let rows ← (originals ++ overlays).mapM fun row => do
    let some selected := snapshot.selected.find? (·.occurrence.key == row.occurrence.key)
      | throwError "incomplete_closure:dtr.final_record"
    recordJson (if selected.bindingOwner == some moduleName then selected else row)
  let (inputs, version) ← moduleSourceInputs env moduleName
  return Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("compatibility_version", toJson version),
    ("inventory", Json.arr ((inventory env).filter
      (·.key.registrationModule == moduleName) |>.map (keyJson ∘ TemplateOccurrenceEvent.key))),
    ("registered", Json.arr (registered.map keyJson)), ("records", Json.arr rows),
    ("inputs", Json.arr (inputs.map inputJson))]

/-- Validate the complete native union around a report transaction. Each native
snapshot is still checked against the loaded image; shared imports are rehashed
once per boundary, rather than once for every module that imports them. Neither
source hashes nor a caller-supplied validation flag can authorize this API. -/
def reportJson (modules : Array (Name × Array TemplateOccurrenceKey)) : MetaM (Array Json) := do
  let env ← getEnv
  let roots := #[`LeanInformationAudit.Registry] ++ modules.map Prod.fst ++
    (if modules.any (fun row => row.1 == env.header.mainModule) then
      env.header.imports.map (·.module) else #[])
  TemplateAudit.NativeCoherence.validate roots
  let snapshot ← exportSnapshot
  let rows ← modules.mapM fun (moduleName, registered) => moduleJson snapshot moduleName registered
  -- Compare the original snapshots after all source hashes and records have
  -- been read. A replacement during this transaction cannot renew them.
  TemplateAudit.NativeCoherence.validate roots
  return rows

end LeanInformationAudit.TemplateBinding

namespace LeanInformationAudit
open Lean Meta


def registerValidatedEntry (entry : InformationRegistryEntry) :
    Lean.Elab.Command.CommandElabM Unit := do
  TemplateBinding.publishRegistration (← registerSemanticEntry entry)

end LeanInformationAudit

namespace LeanInformationAudit
open Lean Meta

/-- Fixed finite producer for environments that have no structural registry.
The standalone inspector requires this owner-bound API whenever Registry occurs
in the actual import closure, including roots with an empty inventory. -/
def finiteInformationTemplateReportDriver : InformationTemplateReportDriver := fun moduleNames => do
  let env ← getEnv
  let modules := moduleNames.map fun moduleName => Id.run do
    let registered := (InformationRegistry.entries env).filter
      (·.registrationModuleName == moduleName) |>.map fun entry => {
        root := moduleName, registrationModule := moduleName, theoremName := entry.theoremName,
        objectArena := entry.canonicalObjectArenaName, «catalog» := entry.effectiveCatalogId :
          TemplateOccurrenceKey }
    return (moduleName, registered ++ (TemplateBinding.familyKeys env).filter
      (·.registrationModule == moduleName))
  TemplateBinding.reportJson modules

end LeanInformationAudit
