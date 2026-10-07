import LeanInformationAudit.ArtifactRegistration
import LeanInformationAudit.CompiledSnapshots
import LeanInformationAudit.Contract.NodeFacts
import Lean.PrivateName

namespace LeanInformationAudit.CompiledSeal
open Lean Contract TemplateAudit

private def localName (store : RawArtifacts.Store) (contract : Option RootCatalogContract)
    (root owner : Name) (suffix : String) : Name :=
  let name := owner.str suffix
  if (store.owners[owner]?).getD root == root then name
  else match contract.bind (·.companionPrefix) with
    | some companionPrefix => companionPrefix ++ name
    | none => mkPrivateNameCore root (privateToUserName name)

private def rootQualified (root : Name) (localNames : Bool)
    (entry : InformationRegistryEntry) : InformationRegistryEntry :=
  if localNames then entry else { entry with
    unitName := catalogQualifiedName root entry.canonicalObjectArenaName
      entry.effectiveCatalogId entry.theoremName theoremUnitSuffix
    realizationName := catalogQualifiedName root entry.canonicalObjectArenaName
      entry.effectiveCatalogId entry.theoremName primitiveRealizationSuffix }

private def groupEntries (entries : Array InformationRegistryEntry)
    : Array (Name × Array InformationRegistryEntry) :=
  entries.foldl (init := #[]) fun groups entry =>
    match groups.findIdx? (fun group => group.1 == entry.canonicalObjectArenaName) with
    | some index => groups.modify index (fun group => (group.1, group.2.push entry))
    | none => groups.push (entry.canonicalObjectArenaName, #[entry])

private def mismatch (root catalog : Name) (component : String) : IO α :=
  throw <| IO.userError s!"IE-C028 AnalysisCertificateMismatch root={root} catalog={catalog} \
    component={component} expected=raw-catalog actual=different"

private def consumeCatalog (store : RawArtifacts.Store) (record : CatalogRecord)
    (input : CompiledSealCatalog) : IO (SealArenaRecord × ConstantInfo) := do
  let find : Name → Option ConstantInfo := fun name => store.constants[name]?
  let view : Contract.NodeFacts.View := {
    find
    owner := fun name => store.owners[name]?
    external := fun name =>
      store.metadata.externs.contains name || store.metadata.implementedBy.contains name }
  let units ← IO.ofExcept <| Contract.NodeFacts.sealFacts view input.facts input.catalogAt
  let fs ← Decoder.fields find ``Contract.SealCatalog input.value 15
  let size ← Decoder.liftLiteral (Literal.nat "seal.size" fs[3]!)
  unless size == record.units.size && units.size == size &&
      input.arenaName == record.arenaName && input.catalogId == record.catalogId do
    mismatch record.rootId record.catalogId "reg-membership"
  -- Each typed table row certifies the actual catalog position. Its item must
  -- be the original Reg operand retained by the independently decoded unit.
  for (unit, item) in record.units.zip units do
    let info ← CompiledRegistration.constant find unit.unitName
    let some value := info.value?
      | mismatch record.rootId record.catalogId s!"reg-vector:{unit.unitName}"
    let item ← IO.ofExcept <| Literal.referencedValue find item
    let value ← IO.ofExcept <| Literal.referencedValue find value
    unless item.equal value do
      mismatch record.rootId record.catalogId s!"reg-vector:{unit.unitName}"
  let raw ← IO.ofExcept <| Literal.referencedValue find input.value
  let levels := raw.getAppFn.constLevels!
  unless levels.length == 2 do throw <| IO.userError "contract.cannot_decode:seal.levels"
  let catalogType := mkApp (mkConst `D5.S3.ConceptDynamics.InformationEscape.Catalog
    (levels ++ [Level.zero])) fs[2]!
  let catalog := mkAppN (mkConst `D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector levels)
    #[fs[2]!, fs[3]!, fs[4]!]
  let parameters := (collectLevelParams (collectLevelParams {} catalogType) catalog).params.toList
  let catalogInfo : ConstantInfo := .defnInfo {
    name := record.catalogName, levelParams := parameters, type := catalogType, value := catalog
    hints := .abbrev, safety := .safe, all := [record.catalogName] }
  return ({ catalog := record, compiledEvidence := true }, catalogInfo)

/-- Reconstruct independent membership, validate every source, rebuild the
complete join and bind the exact kernel-checked unit vector. No publisher or content
driver, command syntax, destination, Environment or kernel capability exists. -/
unsafe def consume (snapshot : Discovery.Snapshot) (owner : Name) (input : SealInput)
    : ArtifactRegistration.M (Array SealArenaRecord) := do
  let state ← get
  let entries := ArtifactRegistration.entriesFor state owner
  let contract := (snapshot.roots.find? (fun row => row.2.rootId == owner)).map Prod.snd
  IO.ofExcept <| CompiledSnapshots.registry (state.store.constants[·]?) owner contract entries
  if entries.isEmpty then throw <| IO.userError "IE-C001 UnregisteredTheoremUnit: registry is empty"
  for entry in entries do
    CompiledRegistration.validateUnique entry entries true
    CompiledRegistration.validateCore (state.store.constants[·]?) entry
    unless entry.compiledMathematics.any (·.bundleNonempty == .evidence) do
      throw <| IO.userError s!"IE-C013 MissingPrimitiveBundle: {entry.theoremName}"
  discard <| ArtifactRegistration.assessJoined owner input.options
  let localNames := entries.all (fun entry => entry.localRegistrationNames && entry.registrationModuleName == owner)
  let qualified := entries.map (rootQualified owner localNames)
  for (source, target) in entries.zip qualified do
    for (oldName, newName) in #[(source.unitName, target.unitName),
        (source.realizationName, target.realizationName)] do
      let contributors := qualifiedNameCollisionEntries (entries ++ qualified) newName target
      let sourceOwner := entries.any (fun entry => (entry.unitName == newName || entry.realizationName == newName) &&
        entry.occurrenceKey == target.occurrenceKey)
      if contributors.size > 1 || ((state.store.constants[newName]?).isSome && !sourceOwner &&
          !(state.generated.contains (newName, owner))) then
        throw <| IO.userError (qualifiedNameCollisionError owner target.effectiveCatalogId newName contributors)
      if oldName != newName then
        let info ← CompiledRegistration.constant ((← get).store.constants[·]?) oldName
        ArtifactRegistration.keepCompanion owner newName
          (mkConst oldName (info.levelParams.map Level.param)) false input.options (some info.levelParams)
  let groups := groupEntries qualified |>.qsort (fun left right => left.1.lt right.1)
  unless groups.size == input.catalogs.size do
    throw <| IO.userError s!"IE-C028 AnalysisCertificateMismatch component=reg-catalog-domain expected={groups.size} actual={input.catalogs.size}"
  let mut records := #[]
  for (arena, entries) in groups do
    let sorted := entries.qsort (fun left right => left.theoremName.lt right.theoremName)
    let catalogId ← IO.ofExcept <| validateMaximalCatalog owner arena sorted
    let matching := input.catalogs.filter (fun row => row.arenaName == arena && row.catalogId == catalogId)
    unless matching.size == 1 do
      throw <| IO.userError "IE-C028 AnalysisCertificateMismatch component=reg-catalog-identity"
    let catalogName := if localNames then localName state.store contract owner arena "__information_catalog"
      else catalogQualifiedName owner arena catalogId arena "__information_catalog"
    let units := sorted.mapIdx fun index entry => {
      theoremName := entry.theoremName, unitName := entry.unitName, realizationName := entry.realizationName
      registrationModuleName := entry.registrationModuleName, index : CatalogUnitRecord }
    let record : CatalogRecord := {
      rootId := owner, catalogId, catalogKind := .canonicalMaximal
      arenaName := arena, catalogName, units, localSealNames := localNames }
    let some matchingInput := matching[0]?
      | throw <| IO.userError "IE-C028 AnalysisCertificateMismatch component=reg-catalog-identity"
    let store := (← get).store
    let consume : IO (SealArenaRecord × ConstantInfo) := do
      try
        return ← consumeCatalog store record matchingInput
      catch error =>
        throw <| IO.userError s!"contract.assessment_failed:{owner}:{matchingInput.source}:{error}"
    let (result, catalogInfo) ← consume
    if let some existing := (← get).store.constants[catalogName]? then
      let same := existing.type.equal catalogInfo.type
      let some value := existing.value? | throw <| IO.userError s!"IE-C009 ProofConstructionFailed:{catalogName}"
      unless same && value.equal (catalogInfo.value?.getD catalogInfo.type) do
        throw <| IO.userError (qualifiedNameCollisionError owner catalogId catalogName sorted)
    modify fun state => { state with
      store := { state.store with
        constants := state.store.constants.insert catalogName catalogInfo
        owners := state.store.owners.insert catalogName owner }
      generated := state.generated.push (catalogName, owner) }
    records := records.push result
  return records

end LeanInformationAudit.CompiledSeal
