import LeanInformationAudit.RegistryTypes
import LeanInformationAudit.Registry
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import Mathlib.Data.Fin.VecNotation

namespace LeanInformationAudit

open Lean
open Lean.Elab.Command
open Lean.Meta
open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape

structure PreparedCatalog where
  record : CatalogRecord
  arenaValue : Expr
  type : Expr
  value : Expr
  declaration : Declaration

private def nameLess (left right : Name) : Bool :=
  left.lt right

private def catalogNameFor (env : Environment) (rootId arenaName : Name) (catalogId : CatalogId)
    (localSealNames : Bool) : Name :=
  if localSealNames then localCompanionName env rootId arenaName "__information_catalog"
  else catalogQualifiedName rootId arenaName catalogId arenaName "__information_catalog"

private def entryArenaValue (entry : InformationRegistryEntry) : MetaM Expr := do
  if entry.objectArenaName.isAnonymous then
    return (← RegistrationGates.normalizeArena (← mkConstWithFreshMVarLevels entry.arenaName)).finite
  else
    mkConstWithFreshMVarLevels entry.objectArenaName

private def propositionIsTrue (proposition : Expr) : MetaM Bool := do
  let decision ← mkDecide proposition
  reduceEval decision

private def validateEntry (rootId : Name) (env : Environment) (entry : InformationRegistryEntry) :
    Lean.Elab.Term.TermElabM Unit := do
  match ← validatePersistedEntry rootId env entry with
  | .ok () => pure ()
  | .error message => throwError message
  let unitExpr := mkConst entry.unitName
  let primitives ← mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.primitives
    #[unitExpr]
  let nonempty ← mkAppM
    `D5.S3.ConceptDynamics.CIRPT.PrimitiveBundle.Nonempty #[primitives]
  unless ← propositionIsTrue nonempty do
    throwError "IE-C013 MissingPrimitiveBundle: {entry.theoremName}"

private initialize sourceValidationEvents : EnvExtension (Array Name) ←
  registerEnvExtension (pure #[])

/-- Read-only observation of actual source-validator invocations. -/
def observedSourceValidations (env : Environment) : Array Name :=
  sourceValidationEvents.getState env

/-- Validate every persisted source entry before any seal declaration is staged. -/
def validateSourceEntries (rootId : Name) (env : Environment)
    (entries : Array InformationRegistryEntry) : CommandElabM Unit := do
  for entry in entries do
    modifyEnv fun current => sourceValidationEvents.modifyState current (·.push entry.theoremName)
    liftTermElabM <| validateEntry rootId env entry

/-- This capability is issued only after source validation and the complete
available binding join. Consumers cannot construct or retarget a snapshot. -/
structure ValidatedSourceSnapshot where
  private mk ::
  rootId : Name
  private environment : Environment
  private options : Options
  private sources : Array InformationRegistryEntry
  private catalogs : Array InformationRegistryEntry
  private bindings : Array BindingRecord

def ValidatedSourceSnapshot.sourceEntries (snapshot : ValidatedSourceSnapshot) :
    Array InformationRegistryEntry := snapshot.sources

private def sameSnapshotObject (a b : α) : Bool := unsafe ptrEq a b

private def ValidatedSourceSnapshot.requireCurrent (snapshot : ValidatedSourceSnapshot) :
    CommandElabM Unit := do
  unless sameRegistrationEnvironment snapshot.environment (← getEnv) &&
      sameSnapshotObject snapshot.options (← getOptions) do
    throwError "IE-C050 ClosedTruthReadout reason=incomplete_closure rule=dtr.snapshot_environment"

/-- The two independent entry points obtain the same validation capability.
Unresolved template metadata is retained separately from mathematical validity. -/
def validateSourceSnapshot (rootId : Name) (entries : Array InformationRegistryEntry) :
    CommandElabM ValidatedSourceSnapshot := do
  if entries.isEmpty then throwError "IE-C001 UnregisteredTheoremUnit: registry is empty"
  let env ← getEnv
  validateSourceEntries rootId env entries
  let bindings ← liftTermElabM do
    TemplateBinding.assessJoined (← RegistrationAssessmentInput.capture rootId)
  return {
    rootId
    environment := ← getEnv
    options := ← getOptions
    sources := entries
    catalogs := entries
    bindings }

/-- Assess a captured input without changing its root to the report host.
The resulting capability remains bound to the assessed environment and options. -/
def assessRegistrationInput (input : RegistrationAssessmentInput) :
    CommandElabM ValidatedSourceSnapshot := do
  unless sameRegistrationEnvironment input.environment (← getEnv) &&
      sameSnapshotObject input.options (← getOptions) do
    throwError "IE-C050 ClosedTruthReadout reason=incomplete_closure rule=dtr.assessment_input"
  validateSourceSnapshot input.rootId (InformationRegistry.forRoot input.environment input.rootId)

/-- Advance a capability through precisely the allowed alias declarations. The
caller supplies desired entries, not a replacement Environment or a success bit. -/
def ValidatedSourceSnapshot.stageAliases (snapshot : ValidatedSourceSnapshot)
    (catalogEntries : Array InformationRegistryEntry) : CommandElabM ValidatedSourceSnapshot := do
  snapshot.requireCurrent
  let env ← getEnv
  let root := snapshot.rootId
  unless snapshot.sources.size == catalogEntries.size do
    throwError "IE-C050 ClosedTruthReadout reason=unclassified_form rule=dtr.snapshot_correspondence"
  let mut aliases : Array (Name × Name) := #[]
  for (source, target) in snapshot.sources.zip catalogEntries do
    let originalNames := { target with
      unitName := source.unitName
      realizationName := source.realizationName }
    unless sameEntry source originalNames do
      throwError "IE-C050 ClosedTruthReadout reason=unclassified_form rule=dtr.snapshot_correspondence"
    for (oldName, newName, suffix) in #[
        (source.realizationName, target.realizationName, primitiveRealizationSuffix),
        (source.unitName, target.unitName, theoremUnitSuffix)] do
      if oldName != newName then
        unless newName == catalogQualifiedName root source.canonicalObjectArenaName
            source.effectiveCatalogId source.theoremName suffix && !env.contains newName &&
            !(aliases.any (·.2 == newName)) do
          throwError "IE-C050 ClosedTruthReadout reason=unclassified_form rule=dtr.snapshot_alias"
        aliases := aliases.push (oldName, newName)
  try
    for (source, target) in aliases do
      let sourceId := mkIdent (`_root_ ++ source)
      let targetId := mkIdent (`_root_ ++ target)
      elabCommand (← `(command| abbrev $targetId := $sourceId))
      -- Type elaboration may instantiate universe names, but the alias body
      -- must be the original constant with its full rigid universe telescope.
      liftTermElabM do
        let original ← getConstInfo source
        let .defnInfo aliasInfo ← getConstInfo target
          | throwError "IE-C050 ClosedTruthReadout reason=incomplete_closure rule=dtr.snapshot_alias"
        let .const name levels := aliasInfo.value
          | throwError "IE-C050 ClosedTruthReadout reason=unclassified_form rule=dtr.snapshot_alias"
        unless name == source && levels == aliasInfo.levelParams.map Level.param &&
            original.levelParams.length == aliasInfo.levelParams.length && aliasInfo.safety == .safe do
          throwError "IE-C050 ClosedTruthReadout reason=unclassified_form rule=dtr.snapshot_alias"
        let expected := original.type.instantiateLevelParams original.levelParams levels
        unless ← RegistrationReifier.exact aliasInfo.type expected do
          throwError "IE-C050 ClosedTruthReadout reason=unclassified_form rule=dtr.snapshot_alias_type"
    return { snapshot with environment := ← getEnv, catalogs := catalogEntries }
  catch error =>
    setEnv env
    throw error

private def makeUnitVector (units : Array Expr) : Lean.Elab.Term.TermElabM Expr := do
  let finZero := mkApp (mkConst ``Fin) (mkNatLit 0)
  let mut vector ← withLocalDeclD `impossible finZero fun impossible => do
    mkLambdaFVars #[impossible] units[0]!
  for unit in units.reverse do
    vector ← mkAppM ``Matrix.vecCons #[unit, vector]
  pure vector

private def nameArrayJson (names : Array Name) : String :=
  (Json.arr <| names.map fun name => Json.str name.toString).compress

private def distinctNames (names : Array Name) : Array Name :=
  names.foldl (init := #[]) fun result name =>
    if result.contains name then result else result.push name

def validateMaximalCatalog (rootId arenaName : Name)
    (entries : Array InformationRegistryEntry) : Except String CatalogId := do
  let maximal := entries.filter fun entry => entry.catalogKind == .canonicalMaximal
  if maximal.isEmpty then
    let occurrences := entries.map (·.theoremName) |>.qsort nameLess
    throw s!"IE-C026 MissingMaximalCatalog root={rootId} arena={arenaName} \
occurrences={nameArrayJson occurrences}"
  let catalogIds := distinctNames (entries.map (·.effectiveCatalogId))
    |>.qsort nameLess
  if catalogIds.size != 1 then
    throw s!"IE-C024 SplitCanonicalArenaCatalog root={rootId} arena={arenaName} \
catalogs={nameArrayJson catalogIds}"
  pure catalogIds[0]!

private def prepareCatalog (rootId arenaName : Name) (localSealNames : Bool)
    (entries : Array InformationRegistryEntry) :
    Lean.Elab.Term.TermElabM PreparedCatalog := do
  let sorted := entries.qsort fun left right => nameLess left.theoremName right.theoremName
  let catalogId <- match validateMaximalCatalog rootId arenaName sorted with
    | .ok catalogId => pure catalogId
    | .error message => throwError message
  let some firstEntry := sorted[0]?
    | throwError "IE-C026 MissingMaximalCatalog root={rootId} arena={arenaName} occurrences=[]"
  let arena ← entryArenaValue firstEntry
  let nondegenerate ← mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.Arena.Nondegenerate #[arena]
  unless ← propositionIsTrue nondegenerate do
    throwError "IE-C004 DegenerateArena: {arenaName}"
  let unitExprs := sorted.map fun entry => mkConst entry.unitName
  let vector ← makeUnitVector unitExprs
  let value ← mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector #[vector]
  -- Preserve the independently selected object arena in the public type.
  -- Inference from a unit can retain its definitionally equal law-arena spelling.
  let inferred ← inferType value
  let type := mkApp inferred.getAppFn arena
  unless ← isDefEq inferred type do
    throwError "IE-C006 StatementProofMismatch: catalog arena {arenaName}"
  let units := sorted.mapIdx fun index entry => {
    theoremName := entry.theoremName
    unitName := entry.unitName
    realizationName := entry.realizationName
    registrationModuleName := entry.registrationModuleName
    index
  }
  let catalogName := catalogNameFor (← getEnv) rootId arenaName catalogId localSealNames
  let declaration := .defnDecl {
    name := catalogName
    levelParams := []
    type
    value
    hints := .abbrev
    safety := .safe
  }
  pure {
    record := {
      rootId
      catalogId
      catalogKind := .canonicalMaximal
      arenaName
      catalogName
      units
      localSealNames
    }
    arenaValue := arena
    type
    value
    declaration
  }

private def groupEntries (entries : Array InformationRegistryEntry) :
    Array (Name × Array InformationRegistryEntry) :=
  entries.foldl (init := #[]) fun groups entry =>
    match groups.findIdx? fun group => group.1 == entry.canonicalObjectArenaName with
    | some index => groups.modify index fun group => (group.1, group.2.push entry)
    | none => groups.push (entry.canonicalObjectArenaName, #[entry])

/-- Catalog construction consumes the capability without repeating source or
binding assessment. Any uncontrolled environment edit invalidates it. -/
def prepareCatalogsFromSnapshot (snapshot : ValidatedSourceSnapshot) :
    CommandElabM (Array PreparedCatalog) := do
  snapshot.requireCurrent
  let env ← getEnv
  let rootId := snapshot.rootId
  let localSealNames := snapshot.sources.all fun entry =>
    entry.localRegistrationNames && entry.registrationModuleName == rootId
  let groups := (groupEntries snapshot.catalogs).qsort fun left right => nameLess left.1 right.1
  let catalogs ← liftTermElabM <| groups.mapM fun group =>
    prepareCatalog rootId group.1 localSealNames group.2
  pure <| catalogs.qsort fun left right =>
    nameLess left.record.catalogId right.record.catalogId ||
      (left.record.catalogId == right.record.catalogId &&
        nameLess left.record.arenaName right.record.arenaName)

/-- Independent callers validate once and use checked alias correspondence. -/
def prepareCatalogsFromEntries (rootId : Name) (sourceEntries catalogEntries :
    Array InformationRegistryEntry) : CommandElabM (Array PreparedCatalog) := do
  let snapshot ← validateSourceSnapshot rootId sourceEntries
  let snapshot ← snapshot.stageAliases catalogEntries
  prepareCatalogsFromSnapshot snapshot

/-- Validate the registry once and prepare catalogs using their original units. -/
def prepareCatalogs (rootId : Name) : CommandElabM (Array PreparedCatalog) := do
  let entries := InformationRegistry.forRoot (← getEnv) rootId
  prepareCatalogsFromEntries rootId entries entries

end LeanInformationAudit
