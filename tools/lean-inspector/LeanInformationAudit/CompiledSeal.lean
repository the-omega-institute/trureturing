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

/-- Canonical class numbers and axis labels are literal certified data. -/
private def primitiveStatistics (classes : Array Nat) (labels : Array Name)
    : Nat × Array String × String := Id.run do
  let mut groups : Array (Array Nat) := #[]
  for ordinal in [:classes.size] do
    let classId := classes[ordinal]!
    if classId == groups.size then groups := groups.push #[ordinal]
    else groups := groups.modify classId (·.push ordinal)
  let serialization := String.intercalate ";" (toString groups.size ::
    groups.toList.map (fun members => String.intercalate "," (members.toList.map toString)))
  let axes := #[
    ("cut", `D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut),
    ("flow", `D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.flow),
    ("admit", `D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.admit),
    ("anchor", `D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.anchor)].foldl
      (fun output pair => output ++ (labels.filter (· == pair.2)).map (fun _ => pair.1)) #[]
  return (labels.size, axes, "sha256:" ++ Sha256.hex serialization.toUTF8)

private def signatureLabel (mask : Nat) : String :=
  String.ofList <| (List.range 4).map (fun coordinate =>
    if mask / (2 ^ (3 - coordinate)) % 2 == 1 then '1' else '0')

private def consumeCatalog (store : RawArtifacts.Store) (record : CatalogRecord)
    (input : CompiledSealCatalog) : IO (SealArenaRecord × ConstantInfo) := do
  let find : Name → Option ConstantInfo := fun name => store.constants[name]?
  let view : Contract.NodeFacts.View := {
    find
    owner := fun name => store.owners[name]?
    external := fun name =>
      store.metadata.externs.contains name || store.metadata.implementedBy.contains name }
  let readout ← IO.ofExcept <| Contract.NodeFacts.sealFacts view input.facts input.catalogAt
  let fs ← Decoder.fields find ``Contract.SealCatalog input.value 15
  let size ← Decoder.liftLiteral (Literal.nat "seal.size" fs[3]!)
  unless size == record.units.size && readout.units == size &&
      input.arenaName == record.arenaName && input.catalogId == record.catalogId do
    mismatch record.rootId record.catalogId "reg-membership"
  let factsReference := input.facts.consumeMData
  let some factsInfo := find factsReference.constName!
    | throw <| IO.userError "contract.cannot_decode:seal.facts_missing"
  let factsValue := Literal.instantiateRawLevels factsInfo.levelParams factsReference.constLevels!
    (factsInfo.value?.getD factsInfo.type)
  let facts ← Decoder.fields find ``Contract.SealFacts factsValue 3
  let units ← IO.ofExcept <| Contract.NodeFacts.table view facts[0]! size
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
  let stateCard ← Decoder.liftLiteral (Literal.nat "seal.stateCard" fs[7]!)
  let full ← Decoder.liftLiteral (Literal.nat "seal.full" fs[9]!)
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
  let nameFor (owner : Name) (suffix : String) := if record.localSealNames then
      owner.str suffix else catalogQualifiedName record.rootId record.arenaName record.catalogId owner suffix
  let literalRows ← IO.ofExcept <| Literal.list "seal.rows"
    (← IO.ofExcept <| Literal.referencedValue find facts[1]!)
  let mut theorems := #[]
  for index in [:record.units.size] do
    let unit := record.units[index]!
    let (unique, without, bins, classes, labels) := readout.rows[index]!
    unless classes.size == stateCard do mismatch record.rootId record.catalogId "reg-state-cardinality"
    let es ← Decoder.fields find ``Contract.SealFactRow literalRows[index]! 8
    let rs ← Decoder.fields find ``Contract.SealRow es[2]! 8
    let conclusion ← Decoder.referencedValue find rs[7]!
    let positive := conclusion.isAppOf ``Contract.SealRowConclusion.positive
    unless positive || conclusion.isAppOf ``Contract.SealRowConclusion.zero do
      throw <| IO.userError "contract.cannot_decode:seal.row_conclusion"
    let name := nameFor unit.theoremName (if positive then "__lowers_escape" else "__trivial_in_catalog")
    let mut roles := #[]
    for bucket in [:bins.size] do
      let count := bins[bucket]!
      if count > 0 then roles := roles.push (signatureLabel (bucket + 1), count)
    let (count, axes, address) := primitiveStatistics classes labels
    theorems := theorems.push {
      theoremName := unit.theoremName, unitName := unit.unitName, realizationName := unit.realizationName
      registrationModuleName := unit.registrationModuleName, index := unit.index
      certificate := if positive then .positive name else .trivial name
      closureCertificate := if positive then none else some (name.str "closure")
      primitiveCount := count, primitiveAxes := axes, primitiveKernelAddress := address
      uniqueCaptureCount := unique, fullEscapeCount := full, withoutEscapeCount := without
      roleSignatureHistogram := roles, proofMethod := "reg-kernel" : SealTheoremRecord }
  let pairs ← Decoder.liftLiteral (Literal.array "seal.collisions" fs[12]!)
  let mut classes : Array (Array Name × Array Name) := #[]
  for pair in pairs do
    let pair ← Decoder.fields find ``Sigma pair 2
    let nested ← Decoder.fields find ``Sigma pair[1]! 2
    let left ← Decoder.fields find ``Fin pair[0]! 2
    let right ← Decoder.fields find ``Fin nested[0]! 2
    let i ← Decoder.liftLiteral (Literal.nat "seal.collision_left" left[0]!)
    let j ← Decoder.liftLiteral (Literal.nat "seal.collision_right" right[0]!)
    unless i < size && j < size && i != j do
      throw <| IO.userError "contract.cannot_decode:seal.collision_index"
    let name := catalogQualifiedName record.rootId record.arenaName record.catalogId record.arenaName
      s!"__kernel_collision_{i}_{j}"
    let left := record.units[i]!.theoremName
    let right := record.units[j]!.theoremName
    if let some index := classes.findIdx? (fun row => row.1[0]? == some left) then
      classes := classes.modify index (fun row => (row.1.push right, row.2.push name))
    else classes := classes.push (#[left, right], #[name])
  let conclusion ← Decoder.referencedValue find fs[13]!
  let redundant := conclusion.isAppOf ``Contract.SealCatalogConclusion.redundant
  unless redundant || conclusion.isAppOf ``Contract.SealCatalogConclusion.irredundant do
    throw <| IO.userError "contract.cannot_decode:seal.catalog_conclusion"
  let verdictName := nameFor record.arenaName
    (if redundant then "__catalog_redundant" else "__catalog_irredundant")
  return ({
    catalog := record, compiledEvidence := true, collisionClasses := classes
    stateEnumeration := some (record.catalogName.str "__zero_state_enumeration")
    verdict := if redundant then .redundant verdictName else .irredundant verdictName
    proofMethod := "reg-kernel", stateCard, offDiagonalPairCount := stateCard * (stateCard - 1)
    fullEscapeCount := full, theorems }, catalogInfo)

/-- Reconstruct independent membership, validate every source, rebuild the
complete join and consume every typed seal field. No publisher or content
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
