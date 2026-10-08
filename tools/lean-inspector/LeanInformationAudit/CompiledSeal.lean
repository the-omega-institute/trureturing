import LeanInformationAudit.ArtifactRegistration
import LeanInformationAudit.CompiledSnapshots
import Lean.PrivateName

namespace LeanInformationAudit.CompiledSeal
open Lean Contract TemplateAudit

private def arenaType := `D5.S3.ConceptDynamics.InformationEscape.Arena
private def lawArenaType := `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena
private def witnessType := `D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord.WitnessArena
private def objectType := `D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena

/-- A finite index data view. The opaque field is never checked, published or
used as evidence; the compiler checked the input function for every index. -/
def indexValue (index size : Nat) : Expr :=
  mkAppN (mkConst ``Fin.mk) #[mkNatLit size, mkNatLit index,
    proofPlaceholder (mkApp2 (mkConst ``Nat.lt) (mkNatLit index) (mkNatLit size))]

private def calculate (context : CompiledExpressions.Context) (action : CompiledExpressions.M α)
    : IO α := return (← CompiledExpressions.run context action).1

private def finiteArena (find : Name → Option ConstantInfo) (entry : InformationRegistryEntry)
    : CompiledExpressions.M Expr := do
  let name := if entry.objectArenaName.isAnonymous then entry.arenaName else entry.objectArenaName
  let info ← CompiledRegistration.constant find name
  let arena := mkConst name (info.levelParams.map Level.param)
  let type ← CompiledExpressions.head info.type
  if type.isConstOf arenaType then return arena
  let law := if type.isConstOf witnessType || type.isConstOf objectType then
      mkApp (mkConst (type.constName!.str "toPrimitiveLawArena") type.constLevels!) arena else arena
  unless type.isConstOf lawArenaType || type.isConstOf witnessType || type.isConstOf objectType do
    throw <| IO.userError s!"contract.cannot_decode:{entry.theoremName}:seal_finite_arena"
  return .proj lawArenaType 0 law

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

private def consumeCatalog (context : CompiledExpressions.Context) (record : CatalogRecord)
    (expectedArena : Expr) (input : CompiledSealCatalog) : IO (SealArenaRecord × ConstantInfo) := do
  let fs ← Decoder.fields context.find `LeanInformationAudit.Contract.SealCatalog input.value 11
  let size ← Decoder.liftLiteral (Literal.nat "seal.size" fs[3]!)
  unless size == record.units.size && input.arenaName == record.arenaName &&
      input.catalogId == record.catalogId do mismatch record.rootId record.catalogId "reg-membership"
  unless ← calculate context (CompiledExpressions.sameShape fs[2]! expectedArena) do
    mismatch record.rootId record.catalogId "reg-arena"
  -- Exhaust the compiler-checked finite function's complete domain. Equality
  -- is computed on its compiled values, rather than proved or kernel-rechecked.
  for unit in record.units do
    let index := indexValue unit.index size
    let unitInfo ← CompiledRegistration.constant context.find unit.unitName
    unless ← calculate context (CompiledExpressions.sameShape (mkApp fs[4]! index)
        (mkConst unit.unitName (unitInfo.levelParams.map Level.param))) do
      mismatch record.rootId record.catalogId s!"reg-vector:{unit.unitName}"
  let raw ← Decoder.referencedValue context.find input.value
  let levels := raw.getAppFn.constLevels!
  unless levels.length == 2 do throw <| IO.userError "contract.cannot_decode:seal.levels"
  let catalog := mkAppN (mkConst `D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector levels)
    #[fs[2]!, mkNatLit size, fs[4]!]
  let catalogType ← calculate context (CompiledExpressions.typeShape catalog)
  let catalogInfo : ConstantInfo := .defnInfo {
    name := record.catalogName, levelParams := [], type := catalogType, value := catalog
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
  let context := CompiledRegistration.expressionContext ((← get).store.constants[·]?)
    (← IO.getNumHeartbeats) input.options
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
    let some firstEntry := sorted[0]?
      | throw <| IO.userError "IE-C026 MissingMaximalCatalog: empty group"
    let expectedArena ← calculate context (finiteArena context.find firstEntry)
    let some matchingInput := matching[0]?
      | throw <| IO.userError "IE-C028 AnalysisCertificateMismatch component=reg-catalog-identity"
    let consume : IO (SealArenaRecord × ConstantInfo) := do
      try
        return ← consumeCatalog context record expectedArena matchingInput
      catch error =>
        throw <| IO.userError s!"contract.assessment_failed:{owner}:{matchingInput.source}:{error}"
    let (result, catalogInfo) ← consume
    if let some existing := (← get).store.constants[catalogName]? then
      let same ← calculate context (CompiledExpressions.sameShape existing.type catalogInfo.type)
      let some value := existing.value? | throw <| IO.userError s!"IE-C009 ProofConstructionFailed:{catalogName}"
      unless same && (← calculate context (CompiledExpressions.sameShape value (catalogInfo.value?.getD catalogInfo.type))) do
        throw <| IO.userError (qualifiedNameCollisionError owner catalogId catalogName sorted)
    modify fun state => { state with
      store := { state.store with
        constants := state.store.constants.insert catalogName catalogInfo
        owners := state.store.owners.insert catalogName owner }
      generated := state.generated.push (catalogName, owner) }
    records := records.push result
  return records

end LeanInformationAudit.CompiledSeal
