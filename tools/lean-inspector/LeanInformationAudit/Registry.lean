import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import Lean

namespace LeanInformationAudit

open Lean
open Lean.Meta

private def theoremUnitName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit

private def primitiveLawArenaName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena

private def primitiveRealizationName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization

private def legacyPrimitiveRealizationName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization

def theoremUnitSuffix := "__information_unit"

def primitiveRealizationSuffix := "__primitive_realization"

def generatedCompanionSuffixes : Array String := #[
  theoremUnitSuffix,
  primitiveRealizationSuffix,
  "__lowers_escape",
  "__escape_enriched",
  "__information_catalog",
  "__catalog_irredundant"
]

abbrev CatalogId := Name

inductive CatalogKind where
  | canonicalMaximal
  | analysisView
  deriving BEq, Inhabited, Repr

def CatalogKind.artifactName : CatalogKind -> String
  | .canonicalMaximal => "canonical_maximal"
  | .analysisView => "analysis_view"

structure InformationRegistryEntry where
  theoremName : Name
  unitName : Name
  /-- The `PrimitiveLawArena` presentation; retained under its v4.1 field name. -/
  arenaName : Name
  /-- The declaration holding the native realization or the legacy witness. -/
  realizationName : Name
  catalogId : CatalogId := .anonymous
  catalogKind : CatalogKind := .canonicalMaximal
  registrationModuleName : Name := .anonymous
  objectArenaName : Name := .anonymous
  /-- False exactly for registrations using the occurrence-aware v4.2 syntax. -/
  legacyNaming : Bool := true

def InformationRegistryEntry.lawArenaName (entry : InformationRegistryEntry) : Name :=
  entry.arenaName

def InformationRegistryEntry.canonicalObjectArenaName
    (entry : InformationRegistryEntry) : Name :=
  if entry.objectArenaName.isAnonymous then entry.arenaName else entry.objectArenaName

def InformationRegistryEntry.effectiveCatalogId
    (entry : InformationRegistryEntry) : CatalogId :=
  if entry.catalogId.isAnonymous then entry.arenaName else entry.catalogId

def InformationRegistryEntry.occurrenceKey
    (entry : InformationRegistryEntry) : Name × Name :=
  (entry.canonicalObjectArenaName, entry.theoremName)

/-- The one naming function used for all v4.2 occurrence companions. -/
def catalogQualifiedName (rootId objectArenaName : Name) (catalogId : CatalogId)
    (theoremName : Name) (suffix : String) : Name :=
  theoremName
    |>.str (rootId.toString ++ "/" ++ objectArenaName.toString ++ "/" ++
      catalogId.toString)
    |>.str suffix

private def jsonNameArray (names : Array Name) : String :=
  (Json.arr <| names.map fun name => Json.str name.toString).compress

private def occurrenceLabel (entry : InformationRegistryEntry) : Name :=
  entry.canonicalObjectArenaName.str entry.theoremName.toString

def qualifiedNameCollisionError (rootId : Name) (catalogId : CatalogId)
    (generatedName : Name) (entries : Array InformationRegistryEntry) : String :=
  let occurrences := entries.map occurrenceLabel |>.qsort (fun left right => left.lt right)
  s!"IE-C025 QualifiedNameCollision root={rootId} catalog={catalogId} \
generated_name={generatedName} occurrences={jsonNameArray occurrences}"

def rejectKernelAddressSemanticUse (rootId : Name) (catalogId : CatalogId)
    (address consumer : String) : Except String Unit :=
  .error s!"IE-C030 KernelAddressUsedAsSemanticEvidence root={rootId} \
catalog={catalogId} address={address} consumer={consumer}"

private initialize informationRegistryExt :
    SimplePersistentEnvExtension InformationRegistryEntry
      (Array InformationRegistryEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.foldl (· ++ ·) #[]
  }

def InformationRegistry.entries (env : Environment) :
    Array InformationRegistryEntry :=
  informationRegistryExt.getState env

def InformationRegistry.find? (env : Environment) (theoremName : Name) :
    Option InformationRegistryEntry :=
  (entries env).find? fun entry => entry.theoremName == theoremName

def InformationRegistry.hasTheorem (env : Environment) (n : Name) : Bool :=
  (find? env n).isSome

def InformationRegistry.hasOccurrence (env : Environment)
    (objectArena theoremName : Name) : Bool :=
  (entries env).any fun entry =>
    entry.canonicalObjectArenaName == objectArena && entry.theoremName == theoremName

def InformationRegistry.hasUnit (env : Environment) (n : Name) : Bool :=
  (entries env).any fun entry => entry.unitName == n

def isCompanionName : Name -> Bool
  | .str _ suffix =>
      generatedCompanionSuffixes.contains suffix
  | _ => false

private def duplicateError (name : Name) : String :=
  s!"IE-C002 DuplicateRegistration: {name}"

private def statementMismatchError (name : Name) : String :=
  s!"IE-C006 StatementProofMismatch: {name}"

/-- Perform the environment-only checks shared by admission and sealing. -/
private def validateEntryDeclarations (env : Environment)
    (entry : InformationRegistryEntry) :
    Except String Unit := do
  if isCompanionName entry.theoremName then
    throw s!"IE-C011 GeneratedCertificateRegistered: {entry.theoremName}"
  match env.find? entry.theoremName with
  | some (.thmInfo _) => pure ()
  | _ => throw s!"IE-C001 UnregisteredTheoremUnit: {entry.theoremName}"
  unless env.contains entry.unitName do
    throw (statementMismatchError entry.theoremName)
  unless env.contains entry.arenaName do
    throw s!"IE-C003 ArenaResolutionFailed: {entry.arenaName}"
  unless env.contains entry.canonicalObjectArenaName do
    throw s!"IE-C003 ArenaResolutionFailed: {entry.canonicalObjectArenaName}"
  unless env.contains entry.realizationName do
    throw (statementMismatchError entry.theoremName)
  let unitInfo := env.find? entry.unitName |>.get!
  unless unitInfo.type.getAppFn.constName? == some theoremUnitName do
    throw (statementMismatchError entry.theoremName)

def compilePrimitiveBundle (arenaExpr realizationExpr : Expr) : MetaM Expr := do
  let realizationType <- instantiateMVars (← whnfR (← inferType realizationExpr))
  unless realizationType.getAppFn.constName? == some primitiveRealizationName do
    throwError "realization type mismatch"
  let realizationArgs := realizationType.getAppArgs
  unless realizationArgs.size == 2 do
    throwError "realization argument mismatch"
  let expectedSignature <- mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.signature
    #[arenaExpr]
  unless ← isDefEq realizationArgs[1]! expectedSignature do
    throwError "realization signature mismatch"
  let arenaValue <- mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena
    #[arenaExpr]
  let stateType <- mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.Arena.State #[arenaValue]
  let stateDecidableEq <- mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.Arena.stateDecidableEq #[arenaValue]
  let compiler <- mkConstWithFreshMVarLevels
    `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle
  return mkAppN compiler
    #[stateType, realizationArgs[1]!, stateDecidableEq, realizationExpr]

/-- Complete the declaration and definitional-equality checks shared by both phases. -/
private def validateEntryCore (env : Environment) (entry : InformationRegistryEntry) :
    MetaM (Except String Unit) := do
  match validateEntryDeclarations env entry with
  | .error message => return .error message
  | .ok () => pure ()
  try
    let theoremExpr <- mkConstWithFreshMVarLevels entry.theoremName
    let theoremType <- instantiateMVars (← whnfR (← inferType theoremExpr))
    let unitExpr <- mkConstWithFreshMVarLevels entry.unitName
    let unitType <- instantiateMVars (← whnfR (← inferType unitExpr))
    unless unitType.getAppFn.constName? == some theoremUnitName do
      return .error (statementMismatchError entry.theoremName)
    let unitArgs := unitType.getAppArgs
    if unitArgs.isEmpty then
      return .error (statementMismatchError entry.theoremName)
    let arenaExpr <- mkConstWithFreshMVarLevels entry.arenaName
    let arenaType <- instantiateMVars (← whnfR (← inferType arenaExpr))
    unless arenaType.getAppFn.constName? == some primitiveLawArenaName do
      return .error s!"IE-C003 ArenaResolutionFailed: {entry.arenaName}"
    let expectedArena <- mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena
      #[arenaExpr]
    let objectArenaExpr <- if entry.objectArenaName.isAnonymous then
      pure expectedArena
    else
      let objectArenaExpr <- mkConstWithFreshMVarLevels entry.objectArenaName
      let objectArenaType <- instantiateMVars (← whnfR (← inferType objectArenaExpr))
      unless objectArenaType.getAppFn.constName? ==
          some `D5.S3.ConceptDynamics.InformationEscape.Arena do
        return .error s!"IE-C003 ArenaResolutionFailed: {entry.objectArenaName}"
      unless ← isDefEq expectedArena objectArenaExpr do
        return .error (statementMismatchError entry.theoremName)
      pure objectArenaExpr
    unless ← isDefEq unitArgs.back! objectArenaExpr do
      return .error (statementMismatchError entry.theoremName)
    let statementExpr <- mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.Statement
      #[unitExpr]
    let statementType <- instantiateMVars (← whnfR statementExpr)
    let proofExpr <- mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.proof
      #[unitExpr]
    let proofType <- instantiateMVars (← whnfR (← inferType proofExpr))
    unless ← isDefEq statementType theoremType do
      return .error (statementMismatchError entry.theoremName)
    unless ← isDefEq proofType statementType do
      return .error (statementMismatchError entry.theoremName)
    let realizationExpr <- mkConstWithFreshMVarLevels entry.realizationName
    let realizationType <- instantiateMVars (← whnfR (← inferType realizationExpr))
    let realizationHead := realizationType.getAppFn.constName?
    if realizationHead == some primitiveRealizationName then
      let expectedLaw <- mkAppM
        `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.Law
        #[arenaExpr, realizationExpr]
      unless ← isDefEq theoremType expectedLaw do
        return .error (statementMismatchError entry.theoremName)
      let primitivesExpr <- mkAppM
        `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.primitives
        #[unitExpr]
      let compiledBundle <- compilePrimitiveBundle arenaExpr realizationExpr
      unless ← isDefEq primitivesExpr compiledBundle do
        return .error (statementMismatchError entry.theoremName)
    else if realizationHead == some legacyPrimitiveRealizationName then
      match env.find? entry.realizationName with
      | some (.thmInfo _) =>
        let legacyArgs := realizationType.getAppArgs
        unless legacyArgs.size == 3 do
          return .error (statementMismatchError entry.theoremName)
        unless ← isDefEq legacyArgs[0]! arenaExpr do
          return .error (statementMismatchError entry.theoremName)
        unless ← isDefEq legacyArgs[1]! theoremType do
          return .error (statementMismatchError entry.theoremName)
        let primitivesExpr <- mkAppM
          `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.primitives
          #[unitExpr]
        let compiledBundle <- compilePrimitiveBundle arenaExpr legacyArgs[2]!
        unless ← isDefEq primitivesExpr compiledBundle do
          return .error (statementMismatchError entry.theoremName)
      | _ => return .error (statementMismatchError entry.theoremName)
    else
      return .error (statementMismatchError entry.theoremName)
    return .ok ()
  catch _ =>
    return .error (statementMismatchError entry.theoremName)

private def sameEntry (left right : InformationRegistryEntry) : Bool :=
  left.theoremName == right.theoremName &&
    left.unitName == right.unitName &&
    left.arenaName == right.arenaName &&
    left.realizationName == right.realizationName &&
    left.effectiveCatalogId == right.effectiveCatalogId &&
    left.catalogKind == right.catalogKind &&
    left.registrationModuleName == right.registrationModuleName &&
    left.canonicalObjectArenaName == right.canonicalObjectArenaName &&
    left.legacyNaming == right.legacyNaming

private def normalizedEntry (env : Environment)
    (entry : InformationRegistryEntry) : InformationRegistryEntry :=
  { entry with
    registrationModuleName := if entry.registrationModuleName.isAnonymous then
      env.header.mainModule
    else
      entry.registrationModuleName }

/-- Validate a prospective entry before insertion; neither registry key may exist yet. -/
def validateNewEntry (env : Environment) (entry : InformationRegistryEntry) :
    MetaM (Except String Unit) := do
  match ← validateEntryCore env entry with
  | .error message => return .error message
  | .ok () => pure ()
  let entries := InformationRegistry.entries env
  let occurrenceMatches := entries.filter fun candidate =>
    candidate.canonicalObjectArenaName == entry.canonicalObjectArenaName &&
      candidate.theoremName == entry.theoremName
  if !occurrenceMatches.isEmpty then
    return .error (duplicateError entry.theoremName)
  let unitMatches := entries.filter fun candidate =>
    candidate.unitName == entry.unitName
  if !unitMatches.isEmpty then
    return .error <| qualifiedNameCollisionError env.header.mainModule
      entry.effectiveCatalogId entry.unitName (unitMatches.push entry)
  let realizationMatches := entries.filter fun candidate =>
    candidate.realizationName == entry.realizationName
  if !realizationMatches.isEmpty then
    return .error <| qualifiedNameCollisionError env.header.mainModule
      entry.effectiveCatalogId entry.realizationName (realizationMatches.push entry)
  return .ok ()

/-- Validate an entry already stored in the persistent registry exactly once. -/
def validatePersistedEntry (env : Environment) (entry : InformationRegistryEntry) :
    MetaM (Except String Unit) := do
  match ← validateEntryCore env entry with
  | .error message => return .error message
  | .ok () => pure ()
  let entries := InformationRegistry.entries env
  let occurrenceMatches := entries.filter fun candidate =>
    candidate.canonicalObjectArenaName == entry.canonicalObjectArenaName &&
      candidate.theoremName == entry.theoremName
  match occurrenceMatches.toList with
  | [candidate] =>
    unless sameEntry candidate entry do
      return .error (duplicateError entry.theoremName)
  | _ => return .error (duplicateError entry.theoremName)
  let unitMatches := entries.filter fun candidate => candidate.unitName == entry.unitName
  match unitMatches.toList with
  | [candidate] =>
    unless sameEntry candidate entry do
      return .error <| qualifiedNameCollisionError env.header.mainModule
        entry.effectiveCatalogId entry.unitName #[candidate, entry]
  | _ => return .error (qualifiedNameCollisionError env.header.mainModule
      entry.effectiveCatalogId entry.unitName unitMatches)
  let realizationMatches := entries.filter fun candidate =>
    candidate.realizationName == entry.realizationName
  match realizationMatches.toList with
  | [candidate] =>
    unless sameEntry candidate entry do
      return .error <| qualifiedNameCollisionError env.header.mainModule
        entry.effectiveCatalogId entry.realizationName #[candidate, entry]
  | _ => return .error (qualifiedNameCollisionError env.header.mainModule
      entry.effectiveCatalogId entry.realizationName realizationMatches)
  return .ok ()

def registerValidatedEntry (entry : InformationRegistryEntry) :
    Lean.Elab.Command.CommandElabM Unit := do
  let entry := normalizedEntry (← getEnv) entry
  let result <- Lean.Elab.Command.liftTermElabM <|
    validateNewEntry (← getEnv) entry
  match result with
  | .ok () => modifyEnv fun env => informationRegistryExt.addEntry env entry
  | .error message => throwError message

end LeanInformationAudit
