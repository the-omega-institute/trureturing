import LeanInformationAudit.ArtifactRegistration
import LeanInformationAudit.CompiledSnapshots
import Lean.PrivateName

namespace LeanInformationAudit.CompiledSeal
open Lean Contract TemplateAudit

private def arenaType := `D5.S3.ConceptDynamics.InformationEscape.Arena
private def lawArenaType := `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena
private def theoremUnitType := `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
private def bundleType := `D5.S3.ConceptDynamics.CIRPT.PrimitiveBundle
private def atomType := `D5.S3.ConceptDynamics.CIRPT.PrimitiveAtom
private def kernelType := `D5.S3.ConceptDynamics.CIRPT.DecidableKernel
private def objectType := `D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena

/-- A finite index data view. The opaque field is never checked, published or
used as evidence; the compiler checked the input function for every index. -/
def indexValue (index size : Nat) : Expr :=
  mkAppN (mkConst ``Fin.mk) #[mkNatLit size, mkNatLit index,
    proofPlaceholder (mkApp2 (mkConst ``Nat.lt) (mkNatLit index) (mkNatLit size))]

private def calculate (context : CompiledExpressions.Context) (action : CompiledExpressions.M α)
    : IO α := return (← CompiledExpressions.run context action).1

private def natural (role : String) (value : Expr) : CompiledExpressions.M Nat := do
  IO.ofExcept <| Literal.nat role (← CompiledExpressions.head value)

private def array (role : String) (value : Expr) : CompiledExpressions.M (Array Expr) := do
  IO.ofExcept <| Literal.array role (← CompiledExpressions.head value)

private def fields (name : Name) (value : Expr) (count : Nat) : CompiledExpressions.M (Array Expr) := do
  let context ← read
  IO.ofExcept <| Literal.fields context.find name (← CompiledExpressions.head value) count

private def finiteArena (find : Name → Option ConstantInfo) (entry : InformationRegistryEntry)
    : CompiledExpressions.M Expr := do
  let name := if entry.objectArenaName.isAnonymous then entry.arenaName else entry.objectArenaName
  let info ← CompiledRegistration.constant find name
  let arena := mkConst name (info.levelParams.map Level.param)
  let type ← CompiledExpressions.head info.type
  if type.isConstOf arenaType then return arena
  let law := if type.isConstOf objectType then
      mkApp (mkConst (type.constName!.str "toPrimitiveLawArena") type.constLevels!) arena else arena
  unless type.isConstOf lawArenaType || type.isConstOf objectType do
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

/-- Primitive axes and kernel classes are output projections of compiled
bundle fields. They never determine seal admission or certificate selection. -/
private def primitiveStatistics (arena unit : Expr) : CompiledExpressions.M
    (Nat × Array String × String) := do
  let bundle := Expr.proj theoremUnitType 0 unit
  let indices ← CompiledExpressions.finiteIndices (.proj bundleType 1 bundle)
  let atoms := indices.map fun index => mkApp (.proj bundleType 3 bundle) index
  let mut axes := #[]
  for atom in atoms do
    let axis ← CompiledExpressions.head (.proj atomType 0 atom)
    let some label := #[("cut", `D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut),
      ("flow", `D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.flow),
      ("admit", `D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.admit),
      ("anchor", `D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.anchor)].find?
        (fun pair => axis.isConstOf pair.2)
      | throw <| IO.userError "contract.cannot_decode:seal.primitive_axis"
    axes := axes.push label.1
  -- Match the existing axis serialization order.
  axes := #["cut", "flow", "admit", "anchor"].foldl
    (fun output label => output ++ axes.filter (· == label)) #[]
  let states ← CompiledExpressions.finiteIndices (.proj arenaType 1 arena)
  let mut classes : Array (Array Nat) := #[]
  for ordinal in [:states.size] do
    let mut selected := none
    for index in [:classes.size] do
      let representative := (classes[index]!)[0]!
      let mut same := true
      for atom in atoms do
        let kernel := Expr.proj atomType 1 atom
        let decision ← CompiledExpressions.head
          (mkApp2 (.proj kernelType 2 kernel) states[ordinal]! states[representative]!)
        if decision.isAppOf ``Decidable.isFalse then
          same := false
          break
        unless decision.isAppOf ``Decidable.isTrue do
          throw <| IO.userError s!"contract.cannot_decode:seal.primitive_relation:{decision.getAppFn.constName?.getD .anonymous}"
      if same then
        selected := some index
        break
    classes := match selected with
      | some index => classes.modify index (·.push ordinal)
      | none => classes.push #[ordinal]
  let serialization := String.intercalate ";" (toString classes.size ::
    classes.toList.map (fun members => String.intercalate "," (members.toList.map toString)))
  return (indices.size, axes, "sha256:" ++ Sha256.hex serialization.toUTF8)

private def signatureLabel (mask : Nat) : String :=
  String.ofList <| (List.range 4).map (fun coordinate =>
    if mask / (2 ^ (3 - coordinate)) % 2 == 1 then '1' else '0')

private def consumeCatalog (context : CompiledExpressions.Context) (record : CatalogRecord)
    (expectedArena : Expr) (input : CompiledSealCatalog) : IO (SealArenaRecord × ConstantInfo) := do
  let fs ← Decoder.fields context.find ``Contract.SealCatalog input.value 15
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
  let stateCard ← Decoder.liftLiteral (Literal.nat "seal.stateCard" fs[7]!)
  let full ← Decoder.liftLiteral (Literal.nat "seal.full" fs[9]!)
  let catalog ← calculate context do
    let type ← CompiledExpressions.head (← CompiledExpressions.typeShape fs[11]!)
    let .forallE _ _ body _ := type
      | throw <| IO.userError "contract.cannot_decode:seal.row_type"
    let body ← CompiledExpressions.head body
    unless body.isAppOfArity ``Contract.SealRow 3 do
      throw <| IO.userError "contract.cannot_decode:seal.row_type"
    return body.getAppArgs[1]!
  let catalogType ← calculate context (CompiledExpressions.typeShape catalog)
  let catalogInfo : ConstantInfo := .defnInfo {
    name := record.catalogName, levelParams := [], type := catalogType, value := catalog
    hints := .abbrev, safety := .safe, all := [record.catalogName] }
  let nameFor (owner : Name) (suffix : String) := if record.localSealNames then
      owner.str suffix else catalogQualifiedName record.rootId record.arenaName record.catalogId owner suffix
  let mut theorems := #[]
  for unit in record.units do
    let index := indexValue unit.index size
    let rs ← calculate context (fields ``Contract.SealRow (mkApp fs[11]! index) 8)
    let unique ← Decoder.liftLiteral (Literal.nat "seal.unique" rs[0]!)
    let without ← Decoder.liftLiteral (Literal.nat "seal.without" rs[2]!)
    let conclusion ← Decoder.referencedValue context.find rs[7]!
    let positive := conclusion.isAppOf ``Contract.SealRowConclusion.positive
    unless positive || conclusion.isAppOf ``Contract.SealRowConclusion.zero do
      throw <| IO.userError "contract.cannot_decode:seal.row_conclusion"
    let name := nameFor unit.theoremName (if positive then "__lowers_escape" else "__trivial_in_catalog")
    let mut roles := #[]
    for bucket in [:15] do
      let count ← calculate context (natural "seal.role_bin" (mkApp rs[4]! (indexValue bucket 15)))
      if count > 0 then roles := roles.push (signatureLabel (bucket + 1), count)
    let unitInfo ← CompiledRegistration.constant context.find unit.unitName
    let (count, axes, address) ← calculate context
      (primitiveStatistics expectedArena (mkConst unit.unitName (unitInfo.levelParams.map Level.param)))
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
    let args := pair.getAppArgs
    let nested := args.back!.getAppArgs
    let i ← calculate context (natural "seal.collision_left" (.proj ``Fin 0 args[args.size - 2]!))
    let j ← calculate context (natural "seal.collision_right" (.proj ``Fin 0 nested[nested.size - 2]!))
    unless i < size && j < size && i != j do
      throw <| IO.userError "contract.cannot_decode:seal.collision_index"
    let name := catalogQualifiedName record.rootId record.arenaName record.catalogId record.arenaName
      s!"__kernel_collision_{i}_{j}"
    let left := record.units[i]!.theoremName
    let right := record.units[j]!.theoremName
    if let some index := classes.findIdx? (fun row => row.1[0]? == some left) then
      classes := classes.modify index (fun row => (row.1.push right, row.2.push name))
    else classes := classes.push (#[left, right], #[name])
  let conclusion ← Decoder.referencedValue context.find fs[13]!
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
