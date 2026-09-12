import LeanInformationAudit.Registry

namespace LeanInformationAudit

open Lean
open Lean.Elab
open Lean.Elab.Command
open Lean.Elab.Term
open Lean.Meta

/-- Retain construction ownership before the builtin elaborator's structure eta
compaction loses it. Metadata has no effect on kernel typing or definitional equality.
Only live forwarding-head traversal consumes this marker; unused arguments do not. -/
private def markArenaConstruction (elaborator : TermElab) : TermElab := fun stx expected => do
  let value ← elaborator stx expected
  let type ← whnfR (← inferType value)
  if type.isAppOf `D5.S3.ConceptDynamics.InformationEscape.Arena ||
      type.isAppOf `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena then
    return mkAnnotation arenaConstructionMarker value
  return value

@[term_elab Lean.Parser.Term.structInst]
private def elabArenaConstruction : TermElab :=
  markArenaConstruction Lean.Elab.Term.StructInst.elabStructInst

@[term_elab Lean.Parser.Term.structInstDefault]
private def elabDefaultArenaConstruction : TermElab :=
  markArenaConstruction Lean.Elab.Term.StructInst.elabStructInstDefault

private def declarationName (id : TSyntax `ident) : CommandElabM Name := do
  let name := id.getId
  if (`_root_).isPrefixOf name then
    return name.replacePrefix `_root_ .anonymous
  return (← getCurrNamespace) ++ name

private def absoluteIdentFrom (ref : Syntax) (name : Name) : Ident :=
  mkIdentFrom ref (`_root_ ++ name)

private def ensureRegisterableName (env : Environment) (entry : InformationRegistryEntry) :
    CommandElabM Unit := do
  if isCompanionName entry.theoremName then
    throwError "IE-C011 GeneratedCertificateRegistered: {entry.theoremName}"
  let duplicates := (InformationRegistry.entries env).filter (·.theoremName == entry.theoremName)
  unless duplicates.isEmpty do
    throwError (duplicateRegistrationError entry (duplicates.push entry))

private def resolveTheorem (id : TSyntax `ident) : CommandElabM Name := do
  let theoremName <- try
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  catch _ =>
    throwErrorAt id
      "IE-C001 UnregisteredTheoremUnit: {← declarationName id}"
  match (← getEnv).find? theoremName with
  | some (.thmInfo _) => pure theoremName
  | _ => throwErrorAt id "IE-C001 UnregisteredTheoremUnit: {theoremName}"

private def witnessName (id : Option (TSyntax `ident)) : CommandElabM Name := do
  match id with
  | none => return .anonymous
  | some id =>
    try liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    catch _ => declarationName id

private def optionalWitnessName (stx : Syntax) : CommandElabM Name := do
  if stx.getNumArgs != 2 then return .anonymous
  witnessName (some ⟨stx[1]⟩)

private def registerEntry (entry : InformationRegistryEntry) : CommandElabM Unit := do
  registerValidatedEntry entry

private def catalogIdFrom (id : TSyntax `ident) : CatalogId :=
  let name := id.getId
  if (`_root_).isPrefixOf name then name.replacePrefix `_root_ .anonymous else name

private def resolveArena (id : TSyntax `ident) : CommandElabM Name := do
  try
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  catch _ =>
    throwErrorAt id "IE-C003 ArenaResolutionFailed: {id.getId}"

private def ensureOccurrenceRegisterable (env : Environment)
    (entry : InformationRegistryEntry) : CommandElabM Unit := do
  if isCompanionName entry.theoremName then
    throwError "IE-C011 GeneratedCertificateRegistered: {entry.theoremName}"
  let duplicates := (InformationRegistry.entries env).filter
    (·.occurrenceKey == entry.occurrenceKey)
  unless duplicates.isEmpty do
    throwError (duplicateRegistrationError entry (duplicates.push entry))
  for generatedName in #[entry.unitName, entry.realizationName] do
    if env.contains generatedName then
      throwError (qualifiedNameCollisionError entry.registrationModuleName
        entry.effectiveCatalogId generatedName
        (qualifiedNameCollisionEntries (InformationRegistry.entries env) generatedName entry))

private def addExpectedOccurrence (theoremId arenaId : TSyntax `ident)
    (registrationModule statementIdentityOverride : String) : CommandElabM Unit := do
  let theoremName <- resolveTheorem theoremId
  let objectArenaName <- resolveArena arenaId
  let env <- getEnv
  let statementIdentity := if statementIdentityOverride.isEmpty then
    theoremStatementIdentity env theoremName
  else
    statementIdentityOverride
  modifyEnv fun current => ExpectedOccurrenceManifest.addEntry current {
    rootId := env.header.mainModule
    objectArenaName
    theoremName
    statementIdentity
    registrationModuleName := registrationModule.toName
  }

/-- Declare one independently expected auxiliary-root occurrence. -/
elab "expect_information_occurrence " theoremId:ident ppLine
    "in " arenaId:ident ppLine
    "from " registrationModule:str : command =>
  addExpectedOccurrence theoremId arenaId registrationModule.getString ""

/-- Negative-fixture form for pinning an independently supplied statement identity. -/
elab "expect_information_occurrence " theoremId:ident ppLine
    "in " arenaId:ident ppLine
    "from " registrationModule:str ppLine
    "statement_id " statementIdentity:str : command =>
  addExpectedOccurrence theoremId arenaId registrationModule.getString
    statementIdentity.getString

private def checkRealizationBundle (theoremName arenaName : Name)
    (typedRealization : Expr) (primitiveTerm : TSyntax `term) : CommandElabM Unit := do
  let valid <- liftTermElabM do
    try
      let arenaExpr <- mkConstWithFreshMVarLevels arenaName
      let typedRealizationType <- instantiateMVars (← whnfR (← inferType typedRealization))
      unless typedRealizationType.getAppFn.constName? ==
          some `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization do
        return false
      let realizationArgs := typedRealizationType.getAppArgs
      unless realizationArgs.size == 2 do
        return false
      let compiledBundle <- compilePrimitiveBundle arenaExpr typedRealization
      let suppliedBundle <- elabTerm primitiveTerm none
      synthesizeSyntheticMVarsNoPostponing
      return ← isDefEq suppliedBundle compiledBundle
    catch _ =>
      return false
  unless valid do
    throwError "IE-C006 StatementProofMismatch: {theoremName}"

private def checkNativeStatement (theoremName arenaName realizationName : Name)
    (statement : TSyntax `term) : CommandElabM Unit := do
  let valid <- liftTermElabM do
    try
      let arenaExpr <- mkConstWithFreshMVarLevels arenaName
      let realizationExpr <- mkConstWithFreshMVarLevels realizationName
      let expectedLaw <- mkAppM
        `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.Law
        #[arenaExpr, realizationExpr]
      let statementExpr <- elabTerm statement (some (mkSort .zero))
      synthesizeSyntheticMVarsNoPostponing
      return ← isDefEq statementExpr expectedLaw
    catch _ =>
      return false
  unless valid do
    throwError "IE-C006 StatementProofMismatch: {theoremName}"

elab "information_theorem " theoremId:ident ppLine
    "in " arenaId:ident ppLine
    "primitives " primitives:term ppLine
    variation:("variation " ident)? sensitivity:("sensitivity " ident)?
    ": " statement:term " := " proof:term : command => do
    let theoremName <- declarationName theoremId
    let arenaName <- try
      liftCoreM <| realizeGlobalConstNoOverloadWithInfo arenaId
    catch _ =>
      throwErrorAt arenaId "IE-C003 ArenaResolutionFailed: {arenaId.getId}"
    let realizationName := theoremName.str primitiveRealizationSuffix
    let unitName := theoremName.str theoremUnitSuffix
    let entry ← liftTermElabM <| prepareRegistrationEntry (← getEnv) {
      theoremName, unitName, arenaName, realizationName }
    ensureRegisterableName (← getEnv) entry
    let realizationId := absoluteIdentFrom theoremId realizationName
    elabCommand (← `(command| def $realizationId :
        D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization
          ($arenaId:ident).signature := $primitives))
    checkNativeStatement theoremName arenaName realizationName statement
    elabCommand (← `(command| theorem $theoremId : $statement := $proof))
    let unitId := absoluteIdentFrom theoremId unitName
    elabCommand (← `(command| def $unitId :
        D5.S3.ConceptDynamics.InformationEscape.TheoremUnit ($arenaId:ident).toArena :=
      { primitives := ($realizationId:ident).toPrimitiveBundle
        Statement := $statement
        proof := $theoremId }))
    registerEntry { entry with
      variationWitness := ← optionalWitnessName (← getRef)[9]
      sensitivityWitness := ← optionalWitnessName (← getRef)[10]
    }

syntax (name := registerInformationTheoremCmd)
  "register_information_theorem " ident ppLine
    "in " ident ppLine
    "primitives " term " realization " ident
    (" variation " ident)? (" sensitivity " ident)? : command

@[command_elab registerInformationTheoremCmd]
private def elabRegisterInformationTheorem : CommandElab := fun stx => do
    let theoremId : TSyntax `ident := ⟨stx[1]⟩
    let arenaId : TSyntax `ident := ⟨stx[3]⟩
    let primitiveTerm : TSyntax `term := ⟨stx[5]⟩
    let realizationId : TSyntax `ident := ⟨stx[7]⟩
    let theoremName <- resolveTheorem theoremId
    let arenaName <- try
      liftCoreM <| realizeGlobalConstNoOverloadWithInfo arenaId
    catch _ =>
      throwErrorAt arenaId "IE-C003 ArenaResolutionFailed: {arenaId.getId}"
    let realizationName <- try
      liftCoreM <| realizeGlobalConstNoOverloadWithInfo realizationId
    catch _ =>
      throwError "IE-C006 StatementProofMismatch: {theoremName}"
    let unitName := localCompanionName (← getEnv) theoremName theoremUnitSuffix
    let entry ← liftTermElabM <| prepareRegistrationEntry (← getEnv) {
      theoremName, unitName, arenaName, realizationName }
    ensureRegisterableName (← getEnv) entry
    match (← getEnv).find? realizationName with
    | some (.thmInfo _) => pure ()
    | _ => throwError "IE-C006 StatementProofMismatch: {theoremName}"
    let theoremExpr <- liftTermElabM <| mkConstWithFreshMVarLevels theoremName
    let theoremType <- liftTermElabM do
      instantiateMVars (← whnfR (← inferType theoremExpr))
    let realizationExpr <- liftTermElabM <| mkConstWithFreshMVarLevels realizationName
    let realizationType <- liftTermElabM do
      instantiateMVars (← whnfR (← inferType realizationExpr))
    let legacyArgs := realizationType.getAppArgs
    unless realizationType.getAppFn.constName? ==
        some `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization &&
        legacyArgs.size == 3 do
      throwError "IE-C006 StatementProofMismatch: {theoremName}"
    let validLegacy <- liftTermElabM do
      return (← isDefEq legacyArgs[0]! (← mkConstWithFreshMVarLevels arenaName)) &&
        (← isDefEq legacyArgs[1]! theoremType)
    unless validLegacy do
      throwError "IE-C006 StatementProofMismatch: {theoremName}"
    checkRealizationBundle theoremName arenaName legacyArgs[2]! primitiveTerm
    let unitId := absoluteIdentFrom theoremId (privateToUserName unitName)
    let unitType <- `(term|
      D5.S3.ConceptDynamics.InformationEscape.TheoremUnit ($arenaId:ident).toArena)
    let unitValue <- `(term|
      D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit
        $realizationId:ident $theoremId:ident)
    if isPrivateName unitName then
      elabCommand (← `(command| private def $unitId : $unitType := $unitValue))
    else
      elabCommand (← `(command| def $unitId : $unitType := $unitValue))
    registerEntry { entry with
      variationWitness := ← optionalWitnessName stx[8]
      sensitivityWitness := ← optionalWitnessName stx[9]
    }

syntax (name := informationTheoremOccurrenceCmd)
  "information_theorem " ident ppLine
    "in " ident ppLine
    "object_arena " ident ppLine
    "catalog " ident ppLine
    "primitives " term ppLine
    ("variation " ident)? ("sensitivity " ident)?
    ": " term " := " term : command

@[command_elab informationTheoremOccurrenceCmd]
private def elabInformationTheoremOccurrence : CommandElab := fun stx => do
  let theoremId : TSyntax `ident := ⟨stx[1]⟩
  let lawArenaId : TSyntax `ident := ⟨stx[3]⟩
  let objectArenaId : TSyntax `ident := ⟨stx[5]⟩
  let catalogId := catalogIdFrom ⟨stx[7]⟩
  let primitiveTerm : TSyntax `term := ⟨stx[9]⟩
  let statementTerm : TSyntax `term := ⟨stx[13]⟩
  let proofTerm : TSyntax `term := ⟨stx[15]⟩
  let theoremName <- declarationName theoremId
  let lawArenaName <- resolveArena lawArenaId
  let objectArenaName <- resolveArena objectArenaId
  let rootId := (← getEnv).header.mainModule
  let unitName := catalogQualifiedName rootId objectArenaName catalogId theoremName
    theoremUnitSuffix
  let realizationName := catalogQualifiedName rootId objectArenaName catalogId theoremName
    primitiveRealizationSuffix
  let entry ← liftTermElabM <| prepareRegistrationEntry (← getEnv) {
    theoremName
    unitName
    arenaName := lawArenaName
    realizationName
    catalogId
    catalogKind := .canonicalMaximal
    registrationModuleName := rootId
    objectArenaName
    localRegistrationNames := false
  }
  ensureOccurrenceRegisterable (← getEnv) entry
  let realizationId := absoluteIdentFrom theoremId realizationName
  elabCommand (← `(command| def $realizationId :
      D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization
        ($lawArenaId:ident).signature := $primitiveTerm))
  checkNativeStatement theoremName lawArenaName realizationName statementTerm
  elabCommand (← `(command| theorem $theoremId : $statementTerm := $proofTerm))
  let unitId := absoluteIdentFrom theoremId unitName
  let unitType <- `(term|
    D5.S3.ConceptDynamics.InformationEscape.TheoremUnit ($objectArenaId:ident))
  let unitValue <- `(term|
    D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.mk
      ($realizationId:ident).toPrimitiveBundle $statementTerm $theoremId)
  elabCommand (← `(command| def $unitId : $unitType := $unitValue))
  registerEntry { entry with
    variationWitness := ← optionalWitnessName stx[10]
    sensitivityWitness := ← optionalWitnessName stx[11]
  }

syntax (name := registerInformationTheoremOccurrenceCmd)
  "register_information_theorem " ident ppLine
    "in " ident ppLine
    "object_arena " ident ppLine
    "catalog " ident ppLine
    "primitives " term " realization " ident
    (" variation " ident)? (" sensitivity " ident)? : command

@[command_elab registerInformationTheoremOccurrenceCmd]
private def elabRegisterInformationTheoremOccurrence : CommandElab := fun stx => do
  let theoremId : TSyntax `ident := ⟨stx[1]⟩
  let lawArenaId : TSyntax `ident := ⟨stx[3]⟩
  let objectArenaId : TSyntax `ident := ⟨stx[5]⟩
  let catalogId := catalogIdFrom ⟨stx[7]⟩
  let primitiveTerm : TSyntax `term := ⟨stx[9]⟩
  let realizationId : TSyntax `ident := ⟨stx[11]⟩
  let theoremName <- resolveTheorem theoremId
  let lawArenaName <- resolveArena lawArenaId
  let objectArenaName <- resolveArena objectArenaId
  let rootId := (← getEnv).header.mainModule
  let unitName := catalogQualifiedName rootId objectArenaName catalogId theoremName
    theoremUnitSuffix
  let realizationName := catalogQualifiedName rootId objectArenaName catalogId theoremName
    primitiveRealizationSuffix
  let entry ← liftTermElabM <| prepareRegistrationEntry (← getEnv) {
    theoremName
    unitName
    arenaName := lawArenaName
    realizationName
    catalogId
    catalogKind := .canonicalMaximal
    registrationModuleName := rootId
    objectArenaName
    localRegistrationNames := false
  }
  ensureOccurrenceRegisterable (← getEnv) entry
  let suppliedRealizationName <- try
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo realizationId
  catch _ =>
    throwError "IE-C006 StatementProofMismatch: {theoremName}"
  let suppliedRealizationInfo <- match (← getEnv).find? suppliedRealizationName with
  | some (.thmInfo info) => pure info
  | _ => throwError "IE-C006 StatementProofMismatch: {theoremName}"
  let theoremExpr <- liftTermElabM <| mkConstWithFreshMVarLevels theoremName
  let theoremType <- liftTermElabM do
    instantiateMVars (← whnfR (← inferType theoremExpr))
  let realizationExpr <- liftTermElabM <|
    mkConstWithFreshMVarLevels suppliedRealizationName
  let realizationType <- liftTermElabM do
    instantiateMVars (← whnfR (← inferType realizationExpr))
  let legacyArgs := realizationType.getAppArgs
  unless realizationType.getAppFn.constName? ==
      some `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization &&
      legacyArgs.size == 3 do
    throwError "IE-C006 StatementProofMismatch: {theoremName}"
  let validLegacy <- liftTermElabM do
    return (← isDefEq legacyArgs[0]! (← mkConstWithFreshMVarLevels lawArenaName)) &&
      (← isDefEq legacyArgs[1]! theoremType)
  unless validLegacy do
    throwError "IE-C006 StatementProofMismatch: {theoremName}"
  checkRealizationBundle theoremName lawArenaName legacyArgs[2]! primitiveTerm
  let realizationLevels := suppliedRealizationInfo.levelParams.map Level.param
  liftCoreM <| addAndCompile <| .thmDecl {
    name := realizationName
    levelParams := suppliedRealizationInfo.levelParams
    type := suppliedRealizationInfo.type
    value := mkConst suppliedRealizationName realizationLevels
  }
  let qualifiedRealizationId := absoluteIdentFrom theoremId realizationName
  let unitId := absoluteIdentFrom theoremId unitName
  let unitType <- `(term|
    D5.S3.ConceptDynamics.InformationEscape.TheoremUnit $objectArenaId:ident)
  let unitValue <- `(term|
    D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit
      $qualifiedRealizationId:ident $theoremId:ident)
  elabCommand (← `(command| def $unitId : $unitType := $unitValue))
  registerEntry { entry with
    variationWitness := ← optionalWitnessName stx[12]
    sensitivityWitness := ← optionalWitnessName stx[13]
  }

end LeanInformationAudit
