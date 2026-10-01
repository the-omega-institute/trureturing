import LeanInformationAudit.ContractPrototype.Replay

namespace LeanInformationAudit.ContractPrototype.Equivalence
open Lean Meta

abbrev NameMapping := Array (Name × Name)

/-- Explicit mappings take priority; namespace prefixes extend componentwise. -/
partial def renameName (mapping : NameMapping) (name : Name) : Name :=
  match mapping.find? (·.1 == name) with
  | some (_, replacement) => replacement
  | none => match name with
    | .str parent component => .str (renameName mapping parent) component
    | .num parent index => .num (renameName mapping parent) index
    | .anonymous => .anonymous

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

def validateConstantImages (env : Environment) (mapping : NameMapping) : MetaM Unit := do
  let mut images : NameMap Name := {}
  for index in [:env.header.moduleNames.size] do
    let owner := env.header.moduleNames[index]!
    if renameName mapping owner == owner then continue
    for name in env.header.moduleData[index]!.constNames do
      let image := renameName mapping name
      if let some earlier := images.find? image then
        unless earlier == name do throwError "contract.mapping:constant_collision:{earlier}/{name}"
      images := images.insert image name

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

private def inEnvironmentForMapping (env : Environment) (action : MetaM α) : MetaM α := do
  let saved ← getEnv
  setEnv (env.setExporting false)
  tryCatchRuntimeEx (do
    let result ← action
    setEnv saved
    return result) fun error => do
      setEnv saved
      throw error

/-- Generated companions are predicted from one side's raw input and the
authorized owner map. Both outputs must match those independent predictions. -/
def completeMapping (oldEnv newEnv : Environment) (prefixes : NameMapping)
    (oldRecord newRecord : BindingRecord) : MetaM NameMapping := do
  let mut mapping ← privateMapping oldEnv newEnv prefixes
  let some (_, input) := (RegistrationInputs.owned oldEnv).find? fun (owner, input) =>
      owner == oldRecord.occurrence.key.registrationModule &&
      input.entry.theoremName == oldRecord.occurrence.key.theoremName
    | throwError "contract.mapping:original_input_missing"
  let entry := input.entry
  let renamed := mappedEntry mapping entry
  let snapshot ← inEnvironmentForMapping newEnv <| discover #[renamed.registrationModuleName]
  let some (_, newInput) := snapshot.registrations.find? fun (owner, input) =>
      owner == renamed.registrationModuleName && input.entry.theoremName == renamed.theoremName
    | throwError "contract.mapping:prototype_input_missing"
  unless newInput.entry.localRegistrationNames == entry.localRegistrationNames &&
      newInput.entry.arenaName == renamed.arenaName &&
      newInput.entry.objectArenaName == renamed.objectArenaName &&
      newInput.entry.catalogId == renamed.catalogId &&
      newInput.entry.sourceBound == entry.sourceBound do
    throwError "contract.mapping:input_identity_changed"
  let oldUnit := inputUnitName oldEnv entry
  let newUnit := inputUnitName newEnv renamed
  unless oldRecord.occurrence.unitName == oldUnit && newRecord.occurrence.unitName == newUnit do
    throwError "contract.mapping:unit_algorithm"
  mapping := mapping.push (oldUnit, newUnit)
  let oldRealization := inputRealizationName oldEnv entry
  if !entry.sourceBound && entry.realizationName == oldRealization then
    mapping := mapping.push (oldRealization, newInput.entry.realizationName)
  unless renameName mapping oldRecord.occurrence.realizationName == newRecord.occurrence.realizationName do
    throwError "contract.mapping:realization_algorithm"
  validateInjection mapping
  validateConstantImages oldEnv mapping
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
