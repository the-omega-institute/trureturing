import LeanInformationAudit.ContractPrototype.Replay

namespace LeanInformationAudit.ContractPrototype.Equivalence
open Lean Meta

abbrev NameMapping := Array (Name × Name)

/-- Supplied by the migration driver before candidate discovery or comparison.
Bridge exceptions are exact source-to-target pairs, never prefixes. -/
structure Authorization where
  owners : NameMapping
  generatedBridges : NameMapping := #[]


/-- Explicit mappings take priority; namespace prefixes extend componentwise. -/
partial def renameName (mapping : NameMapping) (name : Name) : Name :=
  match mapping.find? (·.1 == name) with
  | some (_, replacement) => replacement
  | none => match name with
    | .str parent component => .str (renameName mapping parent) component
    | .num parent index => .num (renameName mapping parent) index
    | .anonymous => .anonymous

def mappedKey (mapping : NameMapping) (key : TemplateOccurrenceKey) : TemplateOccurrenceKey := {
  root := renameName mapping key.root
  registrationModule := renameName mapping key.registrationModule
  theoremName := renameName mapping key.theoremName
  objectArena := renameName mapping key.objectArena
  catalog := renameName mapping key.catalog }

/-- Full occurrence-key bijection. No record can be silently left unconsumed. -/
def pairRecords (mapping : NameMapping) (oldRecords newRecords : Array BindingRecord) :
    MetaM (Array (BindingRecord × BindingRecord)) := do
  for records in #[oldRecords, newRecords] do
    let mut seen : Std.HashSet TemplateOccurrenceKey := {}
    for record in records do
      if seen.contains record.occurrence.key then throwError "contract.pairing:duplicate_key"
      seen := seen.insert record.occurrence.key
  let mut consumed : Std.HashSet TemplateOccurrenceKey := {}
  let mut paired := #[]
  for record in oldRecords do
    let key := mappedKey mapping record.occurrence.key
    let some candidate := newRecords.find? (·.occurrence.key == key)
      | throwError "contract.pairing:missing_key:{key.theoremName}/{key.catalog}"
    if consumed.contains key then throwError "contract.pairing:mapped_duplicate_key"
    consumed := consumed.insert key
    paired := paired.push (record, candidate)
  unless consumed.size == newRecords.size do throwError "contract.pairing:unconsumed_record"
  return paired

/-- The producer and lookup use the same complete occurrence key. -/
def inputKey (entry : InformationRegistryEntry) : TemplateOccurrenceKey := {
  root := entry.registrationModuleName, registrationModule := entry.registrationModuleName
  theoremName := entry.theoremName, objectArena := entry.canonicalObjectArenaName
  catalog := entry.effectiveCatalogId }

def uniqueInput (inputs : Array (Name × RegistrationInput)) (key : TemplateOccurrenceKey) :
    MetaM RegistrationInput := do
  let candidates := inputs.filter fun (owner, input) =>
    owner == key.registrationModule && inputKey input.entry == key
  unless candidates.size == 1 do
    throwError "contract.pairing:input_key_count:{key.theoremName}/{key.catalog}:{candidates.size}"
  let some (_, input) := candidates[0]? | throwError "contract.pairing:input_missing"
  return input

/-- Preserve universes, binders, application shape and metadata. Only declaration
references and projection type names change. No normalization is performed. -/
partial def renameExpr (mapping : NameMapping) : Expr → Expr
  | .const name levels => .const (renameName mapping name) levels
  | .app fn argument => .app (renameExpr mapping fn) (renameExpr mapping argument)
  | .lam name domain body info => .lam name (renameExpr mapping domain) (renameExpr mapping body) info
  | .forallE name domain body info => .forallE name (renameExpr mapping domain) (renameExpr mapping body) info
  | .letE name type value body nondep => .letE name (renameExpr mapping type)
      (renameExpr mapping value) (renameExpr mapping body) nondep
  | .mdata data body => .mdata data (renameExpr mapping body)
  | .proj name index body => .proj (renameName mapping name) index (renameExpr mapping body)
  | other => other


/-- Owner changes are supplied before assessment. No mathematical name or template
selection can authorize its own renaming. Prefix domains and images are disjoint. -/
def validatePrefixes (mapping : NameMapping) : MetaM Unit := do
  for index in [:mapping.size] do
    let (source, target) := mapping[index]!
    unless (`Reg).isPrefixOf source && (`Reg).isPrefixOf target do
      throwError "contract.mapping:unauthorized_owner:{source}/{target}"
    for earlier in [:index] do
      let (a,b) := mapping[earlier]!
      if a.isPrefixOf source || source.isPrefixOf a ||
          b.isPrefixOf target || target.isPrefixOf b then
        throwError "contract.mapping:owner_collision:{source}/{target}"

/-- Explicit mappings must be functions and injective, including generated names. -/
def validateInjection (mapping : NameMapping) : MetaM Unit := do
  for index in [:mapping.size] do
    let (source, target) := mapping[index]!
    for earlier in [:index] do
      let (a,b) := mapping[earlier]!
      if (a == source && b != target) || (a != source && b == target) then
        throwError "contract.mapping:name_collision:{source}/{target}"

/-- Private identities are resolved solely from authorized owner and unchanged
user name. The compared records never supply a target name. -/
def privateMapping (oldEnv newEnv : Environment) (prefixes : NameMapping) : MetaM NameMapping := do
  validatePrefixes prefixes
  for (source, target) in prefixes do
    if oldEnv.contains source || newEnv.contains target then
      throwError "contract.mapping:owner_is_declaration:{source}/{target}"
  let mut mapping := prefixes
  for idx in [:oldEnv.header.moduleNames.size] do
    let owner := oldEnv.header.moduleNames[idx]!
    let newOwner := renameName prefixes owner
    if owner == newOwner then continue
    let some newIdx := newEnv.getModuleIdx? newOwner
      | throwError "contract.mapping:mapped_owner_missing:{newOwner}"
    for name in oldEnv.header.moduleData[idx]!.constNames do
      unless isPrivateName name do continue
      let user := renameName prefixes (privateToUserName name)
      let candidates := newEnv.header.moduleData[newIdx.toNat]!.constNames.filter fun candidate =>
        isPrivateName candidate && privateToUserName candidate == user &&
        newEnv.getModuleIdxFor? candidate == some newIdx
      if candidates.isEmpty then continue
      unless candidates.size == 1 do throwError "contract.mapping:private_ambiguity:{name}"
      mapping := mapping.push (name, candidates[0]!)
  validateInjection mapping
  return mapping

def validateSupportImages (mapping : NameMapping) (support : Array Name) : MetaM Unit := do
  let mut images : NameMap Name := {}
  for name in support do
    let image := renameName mapping name
    if let some earlier := images.find? image then
      unless earlier == name do throwError "contract.mapping:constant_collision:{earlier}/{name}"
    images := images.insert image name

/-- The source target closure includes unchanged constants and metadata names;
other candidate targets imported by a batch driver are outside this support. -/
def validateConstantImages (env : Environment) (root : Name) (mapping : NameMapping)
    (metadata : Array Name) : MetaM Unit := do
  let reachable := reachableModules env root
  let mut support := metadata
  for index in [:env.header.moduleNames.size] do
    if reachable.contains env.header.moduleNames[index]! then
      support := support ++ env.header.moduleData[index]!.constNames
  for (name, owner) in GeneratedDeclarations.entries env do
    if reachable.contains owner then support := support.push name
  for (owner, input) in RegistrationInputs.owned env do
    unless reachable.contains owner do continue
    let e := input.entry
    support := support ++ #[owner, e.theoremName, e.unitName, e.realizationName, e.arenaName,
      e.objectArenaName, e.resolvedArenaName, e.catalogId, e.variationWitness, e.sensitivityWitness]
    support := support ++ input.realizationSource.toArray
    if let some declaration := input.declaration then
      support := support ++ declaration.sourceRecord.toArray ++ declaration.escapeInput.finiteBridge.toArray
      for value in declaration.descriptor.toArray ++ declaration.escapeInput.fromObject.toArray ++
          declaration.escapeInput.continuation.toArray do
        support := support ++ value.getUsedConstants
      if let some selection := declaration.escapeInput.sourceSelection then
        support := support.push selection.owner
        if let some definition := selection.definition then
          support := support ++ #[definition.owner, definition.name]
  for (owner, contract) in RootCatalogs.owned env do
    unless reachable.contains owner do continue
    support := support.push contract.rootId
    support := support ++ contract.companionPrefix.toArray
    for row in contract.expected ++ contract.source ++ contract.baseline do
      support := support ++ #[row.theoremName, row.objectArenaName, row.registrationModuleName]
  for (owner, input) in TemplateEnrollmentInputs.owned env do
    unless reachable.contains owner do continue
    support := support ++ #[owner, input.name] ++ input.constructors
  for (owner, input) in ExpectedOccurrenceManifest.owned env do
    unless reachable.contains owner do continue
    support := support ++ #[input.rootId, input.theoremName, input.objectArenaName,
      input.registrationModuleName]
  for (owner, input) in SealInputs.owned env do
    if reachable.contains owner then support := support.push input.rootId
  validateSupportImages mapping support

/-- Apply the existing naming algorithms to raw input, before comparing outputs. -/
def inputUnitName (env : Environment) (entry : InformationRegistryEntry) : Name :=
  if entry.sourceBound then
    catalogQualifiedName entry.registrationModuleName entry.arenaName .anonymous
      entry.theoremName theoremUnitSuffix
  else if entry.localRegistrationNames then
    localCompanionName env entry.registrationModuleName entry.theoremName theoremUnitSuffix
  else catalogQualifiedName entry.registrationModuleName entry.canonicalObjectArenaName
    entry.catalogId entry.theoremName theoremUnitSuffix

def inputRealizationName (env : Environment) (entry : InformationRegistryEntry) : Name :=
  if entry.localRegistrationNames then
    localCompanionName env entry.registrationModuleName entry.theoremName primitiveRealizationSuffix
  else catalogQualifiedName entry.registrationModuleName entry.canonicalObjectArenaName
    entry.catalogId entry.theoremName primitiveRealizationSuffix

def mappedEntry (mapping : NameMapping) (entry : InformationRegistryEntry) : InformationRegistryEntry := {
  entry with
  theoremName := renameName mapping entry.theoremName
  arenaName := renameName mapping entry.arenaName
  objectArenaName := renameName mapping entry.objectArenaName
  resolvedArenaName := renameName mapping entry.resolvedArenaName
  catalogId := renameName mapping entry.catalogId
  registrationModuleName := renameName mapping entry.registrationModuleName }

/-- Naming branches and companion prefixes are selected from the old lowering
input. Candidate metadata only checks the resulting authorized name. -/
def predictedCompanionName (oldEnv : Environment) (mapping : NameMapping)
    (entry : InformationRegistryEntry) (suffix : String) : Name :=
  let renamed := mappedEntry mapping entry
  if entry.sourceBound && suffix == theoremUnitSuffix then
    catalogQualifiedName renamed.registrationModuleName renamed.arenaName .anonymous
      renamed.theoremName suffix
  else if !entry.localRegistrationNames then
    catalogQualifiedName renamed.registrationModuleName renamed.canonicalObjectArenaName
      renamed.catalogId renamed.theoremName suffix
  else
    let name := renamed.theoremName.str suffix
    let declaringModule := (oldEnv.getModuleIdxFor? entry.theoremName).map fun index =>
      oldEnv.header.moduleNames[index.toNat]!
    if declaringModule.getD oldEnv.header.mainModule == entry.registrationModuleName then name
    else match (RootCatalogs.find? oldEnv entry.registrationModuleName).bind (·.companionPrefix) with
      | some companion => renameName mapping companion ++ name
      | none => mkPrivateNameCore renamed.registrationModuleName (privateToUserName name)

private def inEnvironmentForMapping (env : Environment) (action : MetaM α) : MetaM α := do
  let saved ← getEnv
  setEnv (env.setExporting false)
  tryCatchRuntimeEx (do
    let result ← withCurrHeartbeats action
    setEnv saved
    return result) fun error => do
      setEnv saved
      throw error

/-- Generated companions are predicted from one side's raw input and the
authorized owner map. Both outputs must match those independent predictions. -/
def completeMapping (oldEnv newEnv : Environment) (authorization : Authorization)
    (oldRecord newRecord : BindingRecord) : MetaM NameMapping := do
  validateInjection authorization.generatedBridges
  let prefixes := authorization.owners
  let mut mapping ← privateMapping oldEnv newEnv prefixes
  let input ← uniqueInput (RegistrationInputs.owned oldEnv) oldRecord.occurrence.key
  let entry := input.entry
  let renamed := mappedEntry mapping entry
  let snapshot ← inEnvironmentForMapping newEnv <| discover #[renamed.registrationModuleName]
  let newInput ← uniqueInput snapshot.registrations (mappedKey mapping oldRecord.occurrence.key)
  unless newInput.entry.localRegistrationNames == entry.localRegistrationNames &&
      newInput.entry.arenaName == renamed.arenaName &&
      newInput.entry.objectArenaName == renamed.objectArenaName &&
      newInput.entry.catalogId == renamed.catalogId &&
      newInput.entry.sourceBound == entry.sourceBound do
    throwError "contract.mapping:input_identity_changed"
  let oldUnit := inputUnitName oldEnv entry
  let newUnit := predictedCompanionName oldEnv mapping entry theoremUnitSuffix
  unless oldRecord.occurrence.unitName == oldUnit && newRecord.occurrence.unitName == newUnit do
    throwError "contract.mapping:unit_algorithm"
  mapping := mapping.push (oldUnit, newUnit)
  let oldRealization := inputRealizationName oldEnv entry
  if !entry.sourceBound && entry.realizationName == oldRealization then
    let predicted := (authorization.generatedBridges.find? (·.1 == oldRealization)).map Prod.snd
      |>.getD (predictedCompanionName oldEnv mapping entry primitiveRealizationSuffix)
    unless newInput.entry.realizationName == predicted do
      throwError "contract.mapping:unauthorized_generated_bridge:{oldRealization}/{newInput.entry.realizationName}"
    let oldType := (← inEnvironmentForMapping oldEnv <| getConstInfo oldRealization).type
    let target ← inEnvironmentForMapping newEnv <| getConstInfo predicted
    unless (renameExpr mapping oldType).equal target.type do
      throwError "contract.mapping:generated_bridge_type"
    let targetOwner := (RegistrationReifier.declaringModuleOf newEnv predicted).getD newEnv.header.mainModule
    unless targetOwner == renamed.registrationModuleName do
      throwError "contract.mapping:generated_bridge_owner"
    mapping := mapping.push (oldRealization, predicted)
  else if !entry.sourceBound then
    if let some (_, target) := authorization.generatedBridges.find? (·.1 == entry.realizationName) then
      unless newInput.entry.realizationName == target do
        throwError "contract.mapping:unauthorized_named_bridge"
      let oldType := (← inEnvironmentForMapping oldEnv <| getConstInfo entry.realizationName).type
      let newType := (← inEnvironmentForMapping newEnv <| getConstInfo target).type
      unless oldType.getAppFn == newType.getAppFn && oldType.getAppArgs.size == 3 &&
          newType.getAppArgs.size == 3 &&
          (renameExpr mapping oldType.getAppArgs[1]!).equal newType.getAppArgs[1]! do
        throwError "contract.mapping:named_bridge_interface"
      inEnvironmentForMapping newEnv do
        unless ← isDefEq (← inferType (renameExpr mapping oldType.getAppArgs[2]!))
            (← inferType newType.getAppArgs[2]!) do
          throwError "contract.mapping:named_bridge_actual_type"
      unless (RegistrationReifier.declaringModuleOf newEnv target).getD newEnv.header.mainModule ==
          renamed.registrationModuleName do throwError "contract.mapping:named_bridge_owner"
      mapping := mapping.push (entry.realizationName, target)
  unless renameName mapping oldRecord.occurrence.realizationName == newRecord.occurrence.realizationName do
    throwError "contract.mapping:realization_algorithm"
  validateInjection mapping
  let key := oldRecord.occurrence.key
  validateConstantImages oldEnv key.root mapping
    #[key.root, key.registrationModule, key.theoremName, key.objectArena, key.catalog,
      oldRecord.occurrence.unitName, oldRecord.occurrence.realizationName]
  return mapping

/-- JSON names change only in schema-designated identity fields. Paths, labels,
diagnostics, hashes, readout data and all other strings remain byte-identical. -/
def renameNameText (mapping : NameMapping) (value : Json) : Json :=
  match value with
  | .str text =>
    match mapping.find? (·.1.toString == text) with
    | some (_, target) => .str target.toString
    | none => .str (renameName mapping text.toName).toString
  | other => other

def renameSourceBinding (mapping : NameMapping) (value : Json) : Json :=
  match value with
  | .obj fields => Json.mkObj (fields.toArray.toList.map fun (key, item) =>
    (key, if key == "source_owner" || key == "source_name" then renameNameText mapping item
      else if key == "definition_entry" || key == "finite_projection" then
        match item with
        | .obj nested => Json.mkObj (nested.toArray.toList.map fun (field, body) =>
          let names := if key == "definition_entry" then #["name", "owner"]
            else #["family_arena", "bridge"]
          (field, if names.contains field then renameNameText mapping body else body))
        | other => other
      else item))
  | other => other

end LeanInformationAudit.ContractPrototype.Equivalence
