import LeanInformationAuditInterface.Syntax
import LeanInformationAudit.Registry

namespace LeanInformationAudit

open Lean
open Lean.Elab
open Lean.Elab.Command
open Lean.Elab.Term
open Lean.Meta

run_cmd TemplateAudit.initializeGrammarPins

/-- Retain construction ownership before the builtin elaborator's structure eta
compaction loses it. Metadata has no effect on kernel typing or definitional equality.
Only live forwarding-head traversal consumes this marker; unused arguments do not. -/
private def markArenaConstruction (elaborator : TermElab) : TermElab := fun stx expected => do
  let value ← elaborator stx expected
  let type ← whnfR (← inferType value)
  if type.isAppOf `D5.S3.ConceptDynamics.InformationEscape.Arena ||
      type.isAppOf `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena ||
      type.isAppOf RegistrationGates.witnessArenaName then
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
  -- Source evidence is acquired by the declaration command, before IO-free sealing.
  discard <| liftTermElabM <| resolveCanonicalArenaName objectArenaName
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
@[command_elab command___In__From_]
private def elabExpectedOccurrence : CommandElab := fun stx =>
  addExpectedOccurrence ⟨stx[1]⟩ ⟨stx[4]⟩ (TSyntax.getString ⟨stx[7]⟩) ""

/-- Negative-fixture form for pinning an independently supplied statement identity. -/
@[command_elab command___In__From__Statement_id_]
private def elabExpectedOccurrenceWithIdentity : CommandElab := fun stx =>
  addExpectedOccurrence ⟨stx[1]⟩ ⟨stx[4]⟩
    (TSyntax.getString ⟨stx[7]⟩) (TSyntax.getString ⟨stx[10]⟩)

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

/-- Elaborate an inline legacy bridge at the imported theorem's exact type and
publish it under the registration-owned companion name. -/
private def addInlineLegacyRealization (theoremName arenaName realizationName : Name)
    (realizationTerm proofTerm : TSyntax `term) : CommandElabM Unit := do
  try
    let (expected, proof, levelParams) ← liftTermElabM do
      let theoremInfo ← getConstInfo theoremName
      withLevelNames theoremInfo.levelParams do
        let statement := theoremInfo.type
        let arena ← mkConstWithFreshMVarLevels arenaName
        let signature ← mkAppM
          `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.signature #[arena]
        let realizationType ← mkAppM
          `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization #[signature]
        let realization ← elabTerm realizationTerm (some realizationType)
        synthesizeSyntheticMVarsNoPostponing
        let realization ← instantiateMVars realization
        let expected ← mkAppM
          `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization
          #[arena, statement, realization]
        let proof ← elabTerm proofTerm (some expected)
        synthesizeSyntheticMVarsNoPostponing
        unless ← isDefEq (← inferType proof) expected do
          throwError "inline realization proof has the wrong type"
        let expected ← levelMVarToParam (← instantiateMVars expected)
        let proof ← levelMVarToParam (← instantiateMVars proof)
        let expectedParams := (collectLevelParams {} expected).params.toList
        let proofOnlyParams := (collectLevelParams {} proof).params.toList.filter
          (!expectedParams.contains ·)
        let proof := proof.instantiateLevelParams proofOnlyParams
          (proofOnlyParams.map fun _ => .zero)
        let levelParams :=
          (collectLevelParams (collectLevelParams {} expected) proof).params.toList
        return (expected, proof, levelParams)
    if (← get).messages.hasErrors then
      throwError "IE-C006 StatementProofMismatch: {theoremName}"
    let valid ← liftTermElabM do
      addAndCompile <| .thmDecl {
        name := realizationName
        levelParams := levelParams
        type := expected
        value := proof }
      let closedExpected := expected.instantiateLevelParams levelParams
        (levelParams.map fun _ => .zero)
      withoutModifyingState <| RegistrationGates.checked realizationName closedExpected
    unless valid && !(← get).messages.hasErrors do
      throwError "IE-C006 StatementProofMismatch: {theoremName}"
  catch error =>
    if error.isRuntime then throw error
    throwError "IE-C006 StatementProofMismatch: {theoremName}"

/-- Resolve the established named bridge or create the disjoint inline form.
The Boolean records whether the returned theorem already has its final name. -/
private def resolveLegacyRealization (theoremName arenaName generatedName : Name)
    (stx : TSyntax `informationRealization) : CommandElabM (Name × Bool) := do
  if stx.raw.getKind == ``namedInformationRealization then
    let id : TSyntax `ident := ⟨stx.raw[0]⟩
    let name ← try
      liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    catch _ =>
      throwError "IE-C006 StatementProofMismatch: {theoremName}"
    return (name, false)
  if stx.raw.getKind == ``inlineInformationRealization then
    addInlineLegacyRealization theoremName arenaName generatedName
      ⟨stx.raw[1]⟩ ⟨stx.raw[3]⟩
    return (generatedName, true)
  throwError "IE-C006 StatementProofMismatch: {theoremName}"

/-- Package an inline bridge with the imported theorem without re-elaborating
either declaration through syntax. -/
private def addInlineLegacyUnit (theoremName realizationName unitName : Name) :
    CommandElabM Unit := do
  liftTermElabM do
    let realizationInfo ← getConstInfo realizationName
    let theoremInfo ← getConstInfo theoremName
    let realization := Lean.mkConst realizationName
      (realizationInfo.levelParams.map Level.param)
    let theoremExpr := Lean.mkConst theoremName
      (theoremInfo.levelParams.map Level.param)
    let unit ← mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit
      #[realization, theoremExpr]
    discard <| inferType unit
    let unit ← levelMVarToParam (← instantiateMVars unit)
    let unitType ← levelMVarToParam (← instantiateMVars (← inferType unit))
    let levelParams :=
      (collectLevelParams (collectLevelParams {} unitType) unit).params.toList
    addAndCompile <| .defnDecl {
      name := unitName
      levelParams := levelParams
      type := unitType
      value := unit
      hints := .abbrev
      safety := .safe }

/-- Transaction boundary shared by registration and exception-injection controls. -/
def registrationTransaction (action : CommandElabM Unit) : CommandElabM Unit := do
  -- Command.tryCatch deliberately skips interrupts. At this boundary every
  -- exception must restore the environment, including extension entries.
  let _ : MonadExceptOf Exception CommandElabM := {
    throw := throw
    tryCatch := fun body handler ctx state =>
      try body ctx state catch e => handler e ctx state }
  let saved ← getEnv
  let previousMessages := (← get).messages
  modify fun s => { s with messages := {} }
  try
    action
  catch e =>
    setEnv saved
    if e.isRuntime then throwError "P1.IncompleteCheck: {e.toMessageData}"
    throw e
  finally
    let messages := (← get).messages
    if messages.hasErrors then setEnv saved
    let classify := fun (m : Message) =>
      if m.severity == .error && (Exception.error .missing m.data).isRuntime then
        { m with data := m!"P1.IncompleteCheck: {m.data}" }
      else m
    modify fun s => { s with messages := previousMessages ++ { messages with
      reported := messages.reported.map classify, unreported := messages.unreported.map classify } }

@[command_elab informationTheoremCmd]
private def elabInformationTheorem : CommandElab := fun stx => registrationTransaction do
    let theoremId : TSyntax `ident := ⟨stx[1]⟩
    let arenaId : TSyntax `ident := ⟨stx[3]⟩
    let primitiveTerm : TSyntax `term := ⟨stx[5]⟩
    let statement : TSyntax `term := ⟨stx[9]⟩
    let proof : TSyntax `term := ⟨stx[11]⟩
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
          ($arenaId:ident).signature := $primitiveTerm))
    checkNativeStatement theoremName arenaName realizationName statement
    elabCommand (← `(command| theorem $theoremId : $statement := $proof))
    let unitId := absoluteIdentFrom theoremId unitName
    elabCommand (← `(command| def $unitId :
        D5.S3.ConceptDynamics.InformationEscape.TheoremUnit ($arenaId:ident).toArena :=
      { primitives := ($realizationId:ident).toPrimitiveBundle
        Statement := $statement
        proof := $theoremId }))
    registerEntry { entry with
      variationWitness := ← optionalWitnessName stx[6]
      sensitivityWitness := ← optionalWitnessName stx[7]
    }

@[command_elab registerInformationTheoremViaCmd]
private def elabRegisterInformationTheoremVia : CommandElab := fun stx => registrationTransaction do
  let theoremId : TSyntax `ident := ⟨stx[1]⟩
  let arenaName ← resolveArena ⟨stx[5]⟩
  let arena ← liftTermElabM <| RegistrationReifier.freezeArena arenaName
  liftTermElabM do
    for provider in #[RegistrationReifier.pointwiseProvider,
        RegistrationReifier.sensitivityProvider, RegistrationReifier.variationProvider] do
      discard <| RegistrationReifier.checkedProvider provider
  let descriptor ← liftTermElabM do
    let value ← elabTerm stx[3] none
    synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    RegistrationReifier.closed value
    return value
  if (← get).messages.hasErrors then return
  let outputEvidence ← liftTermElabM do
    if stx[6].getNumArgs == 0 then return none
    discard <| RegistrationReifier.semanticSource descriptor
    let expected ← mkAppM ``Nontrivial #[descriptor.getAppArgs[1]!]
    let value ← elabTerm stx[6][1] (some expected)
    synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    RegistrationReifier.closed value
    return some value
  if (← get).messages.hasErrors then return
  let theoremName ← resolveTheorem theoremId
  let unitName := localCompanionName (← getEnv) theoremName theoremUnitSuffix
  let realizationName := localCompanionName (← getEnv) theoremName primitiveRealizationSuffix
  let entry ← liftTermElabM <| prepareRegistrationEntry (← getEnv) {
    theoremName, unitName, arenaName, realizationName,
    statementIdentity := theoremStatementIdentity (← getEnv) theoremName }
  ensureRegisterableName (← getEnv) entry
  let entry ← liftTermElabM <| RegistrationReifier.derive entry arena descriptor outputEvidence
  if (← get).messages.hasErrors then return
  registerEntry entry

@[command_elab registerInformationTheoremCmd]
private def elabRegisterInformationTheorem : CommandElab := fun stx => registrationTransaction do
    let theoremId : TSyntax `ident := ⟨stx[1]⟩
    let arenaId : TSyntax `ident := ⟨stx[3]⟩
    let primitiveTerm : TSyntax `term := ⟨stx[5]⟩
    let realizationSyntax : TSyntax `informationRealization := ⟨stx[7]⟩
    let theoremName <- resolveTheorem theoremId
    let arenaName <- try
      liftCoreM <| realizeGlobalConstNoOverloadWithInfo arenaId
    catch _ =>
      throwErrorAt arenaId "IE-C003 ArenaResolutionFailed: {arenaId.getId}"
    let generatedRealizationName :=
      localCompanionName (← getEnv) theoremName primitiveRealizationSuffix
    let (realizationName, isInline) ← resolveLegacyRealization theoremName arenaName
      generatedRealizationName realizationSyntax
    let unitName := localCompanionName (← getEnv) theoremName theoremUnitSuffix
    let entry ← liftTermElabM <| prepareRegistrationEntry (← getEnv) {
      theoremName, unitName, arenaName, realizationName }
    ensureRegisterableName (← getEnv) entry
    let realizationInfo ← match (← getEnv).find? realizationName with
    | some (.thmInfo info) => pure info
    | _ => throwError "IE-C006 StatementProofMismatch: {theoremName}"
    let theoremType ← if isInline then
      pure (← getConstInfo theoremName).type
    else do
      let theoremExpr ← liftTermElabM <| mkConstWithFreshMVarLevels theoremName
      liftTermElabM do instantiateMVars (← whnfR (← inferType theoremExpr))
    let realizationType ← if isInline then
      pure realizationInfo.type
    else do
      let realizationExpr ← liftTermElabM <| mkConstWithFreshMVarLevels realizationName
      liftTermElabM do instantiateMVars (← whnfR (← inferType realizationExpr))
    let legacyArgs := realizationType.getAppArgs
    unless (realizationType.getAppFn.constName? ==
        (some `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization) ||
        realizationType.getAppFn.constName? == some TemplateAudit.escapeForwardBridge ||
        realizationType.getAppFn.constName? == some RegistrationGates.witnessBridgeName) &&
        legacyArgs.size == 3 do
      throwError "IE-C006 StatementProofMismatch: {theoremName}"
    let validLegacy <- liftTermElabM do
      return (← isDefEq legacyArgs[0]! (← mkConstWithFreshMVarLevels arenaName)) &&
        (← isDefEq legacyArgs[1]! theoremType)
    unless validLegacy do
      throwError "IE-C006 StatementProofMismatch: {theoremName}"
    checkRealizationBundle theoremName arenaName legacyArgs[2]! primitiveTerm
    let variationName ← optionalWitnessName stx[8]
    let sensitivityName ← optionalWitnessName stx[9]
    if realizationType.isAppOf RegistrationGates.witnessBridgeName then
      liftTermElabM do
        let arena ← mkConstWithFreshMVarLevels arenaName
        discard <| RegistrationGates.witnessStatement arena legacyArgs[1]! theoremName
        if let some diagnostic ← RegistrationGates.witnessEvidence arena legacyArgs[2]!
            variationName sensitivityName then throwError diagnostic
    if realizationType.isAppOf TemplateAudit.escapeForwardBridge &&
        (stx[8].getNumArgs == 0 || stx[9].getNumArgs == 0) then
      throwError "unclassified_form:dtr.forward_bridge_requires_sensitivity"
    if isInline then
      addInlineLegacyUnit theoremName realizationName unitName
    else
      let realizationId : TSyntax `ident := ⟨realizationSyntax.raw[0]⟩
      let unitId := absoluteIdentFrom theoremId (privateToUserName unitName)
      let unitType <- `(term|
        D5.S3.ConceptDynamics.InformationEscape.TheoremUnit ($arenaId:ident).toArena)
      let witnessUnitId := absoluteIdentFrom theoremId (RegistrationGates.witnessBridgeName.str "toTheoremUnit")
      let variationId := absoluteIdentFrom theoremId variationName
      let unitValue <- if realizationType.isAppOf RegistrationGates.witnessBridgeName then
          `(term| $witnessUnitId:ident
            $realizationId:ident (And.left $variationId:ident))
        else if realizationType.isAppOf TemplateAudit.escapeForwardBridge then
          `(term| { primitives := $primitiveTerm, Statement := _, proof := $theoremId:ident })
        else `(term|
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

@[command_elab informationTheoremOccurrenceCmd]
private def elabInformationTheoremOccurrence : CommandElab := fun stx => registrationTransaction do
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

@[command_elab registerInformationTheoremOccurrenceCmd]
private def elabRegisterInformationTheoremOccurrence : CommandElab := fun stx => registrationTransaction do
  let theoremId : TSyntax `ident := ⟨stx[1]⟩
  let lawArenaId : TSyntax `ident := ⟨stx[3]⟩
  let objectArenaId : TSyntax `ident := ⟨stx[5]⟩
  let catalogId := catalogIdFrom ⟨stx[7]⟩
  let primitiveTerm : TSyntax `term := ⟨stx[9]⟩
  let realizationSyntax : TSyntax `informationRealization := ⟨stx[11]⟩
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
  let (suppliedRealizationName, isInline) ← resolveLegacyRealization theoremName
    lawArenaName realizationName realizationSyntax
  let suppliedRealizationInfo <- match (← getEnv).find? suppliedRealizationName with
  | some (.thmInfo info) => pure info
  | _ => throwError "IE-C006 StatementProofMismatch: {theoremName}"
  let theoremType ← if isInline then
    pure (← getConstInfo theoremName).type
  else do
    let theoremExpr ← liftTermElabM <| mkConstWithFreshMVarLevels theoremName
    liftTermElabM do instantiateMVars (← whnfR (← inferType theoremExpr))
  let realizationType ← if isInline then
    pure suppliedRealizationInfo.type
  else do
    let realizationExpr ← liftTermElabM <|
      mkConstWithFreshMVarLevels suppliedRealizationName
    liftTermElabM do instantiateMVars (← whnfR (← inferType realizationExpr))
  let legacyArgs := realizationType.getAppArgs
  unless (realizationType.getAppFn.constName? ==
      (some `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization) ||
        realizationType.getAppFn.constName? == some TemplateAudit.escapeForwardBridge ||
        realizationType.getAppFn.constName? == some RegistrationGates.witnessBridgeName) &&
      legacyArgs.size == 3 do
    throwError "IE-C006 StatementProofMismatch: {theoremName}"
  let validLegacy <- liftTermElabM do
    return (← isDefEq legacyArgs[0]! (← mkConstWithFreshMVarLevels lawArenaName)) &&
      (← isDefEq legacyArgs[1]! theoremType)
  unless validLegacy do
    throwError "IE-C006 StatementProofMismatch: {theoremName}"
  checkRealizationBundle theoremName lawArenaName legacyArgs[2]! primitiveTerm
  let variationName ← optionalWitnessName stx[12]
  let sensitivityName ← optionalWitnessName stx[13]
  if realizationType.isAppOf RegistrationGates.witnessBridgeName then
    liftTermElabM do
      let arena ← mkConstWithFreshMVarLevels lawArenaName
      discard <| RegistrationGates.witnessStatement arena legacyArgs[1]! theoremName
      if let some diagnostic ← RegistrationGates.witnessEvidence arena legacyArgs[2]!
          variationName sensitivityName then throwError diagnostic
  unless isInline do
    let realizationLevels := suppliedRealizationInfo.levelParams.map Level.param
    liftCoreM <| addAndCompile <| .thmDecl {
      name := realizationName
      levelParams := suppliedRealizationInfo.levelParams
      type := suppliedRealizationInfo.type
      value := mkConst suppliedRealizationName realizationLevels
    }
  let unitId := absoluteIdentFrom theoremId unitName
  let unitType <- `(term|
    D5.S3.ConceptDynamics.InformationEscape.TheoremUnit $objectArenaId:ident)
  if realizationType.isAppOf TemplateAudit.escapeForwardBridge &&
      (stx[12].getNumArgs == 0 || stx[13].getNumArgs == 0) then
    throwError "unclassified_form:dtr.forward_bridge_requires_sensitivity"
  if isInline then
    addInlineLegacyUnit theoremName realizationName unitName
  else
    let qualifiedRealizationId := absoluteIdentFrom theoremId realizationName
    let witnessUnitId := absoluteIdentFrom theoremId (RegistrationGates.witnessBridgeName.str "toTheoremUnit")
    let variationId := absoluteIdentFrom theoremId variationName
    let unitValue <- if realizationType.isAppOf RegistrationGates.witnessBridgeName then
        `(term| $witnessUnitId:ident
          $qualifiedRealizationId:ident (And.left $variationId:ident))
      else if realizationType.isAppOf TemplateAudit.escapeForwardBridge then
        `(term| { primitives := $primitiveTerm, Statement := _, proof := $theoremId:ident })
      else `(term|
        D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit
          $qualifiedRealizationId:ident $theoremId:ident)
    elabCommand (← `(command| def $unitId : $unitType := $unitValue))
  registerEntry { entry with
    variationWitness := ← optionalWitnessName stx[12]
    sensitivityWitness := ← optionalWitnessName stx[13]
  }

end LeanInformationAudit

namespace LeanInformationAudit
open Lean Elab Command

private def elaborateTemplateEnrollment (id : TSyntax `ident)
    (version : Nat) (types : Array (TSyntax `ident)) : CommandElabM Unit := registrationTransaction do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  unless version == 1 do
    logWarning m!"IE-C050 ClosedTruthReadout template={name} reason=unclassified_form rule=E4c.version"
    return
  let constructors ← types.mapM fun ast => liftCoreM <| realizeGlobalConstNoOverloadWithInfo ast
  match ← TemplateAudit.enroll name constructors with
  | .ok () => pure ()
  | .error message =>
    logWarning m!"IE-C050 ClosedTruthReadout template={name} {TemplateAudit.diagnosticFields message}"

@[command_elab command__]
private def elabTemplateEnrollment : CommandElab := fun stx =>
  elaborateTemplateEnrollment ⟨stx[1]⟩ 1 #[]

@[command_elab «command__Constructors_[_,,]»]
private def elabTemplateConstructorsEnrollment : CommandElab := fun stx =>
  elaborateTemplateEnrollment ⟨stx[1]⟩ (TSyntax.getNat ⟨stx[3]⟩)
    (stx[5].getSepArgs.map fun id => ⟨id⟩)

end LeanInformationAudit

namespace LeanInformationAudit
open Lean Meta Elab Command Term

private partial def descriptorHead (stx : Syntax) : Option Syntax :=
  if stx.isIdent then some stx
  else if stx.getKind == ``Parser.Term.paren then descriptorHead stx[1]
  else if stx.getKind == ``Parser.Term.app then descriptorHead stx[0]
  else none

/-- Resolve the written head first so a missing template is evidence failure.
Other term/type errors keep the standard elaborator's error/rollback behavior. -/
def elaborateReadoutDescriptor (term : TSyntax `term) : CommandElabM (Option Expr × Option String) := do
  if let some head := descriptorHead term then
    let resolved ← try
      discard <| liftCoreM <| realizeGlobalConstNoOverloadWithInfo head
      pure true
    catch _ => pure false
    unless resolved do return (none, some "unclassified_form:dtr.missing_template")
  let value ← liftTermElabM do
    let value ← elabTerm term none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars value
  return (some value, none)

private def elaborateEscapeInput (origin residual : Syntax) : CommandElabM EscapeRecordInput := do
  let elaborate (stx : Syntax) : CommandElabM Expr := liftTermElabM do
    let value ← elabTerm stx none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars value
  let fromObject ← if origin.getNumArgs == 0 then pure none
    else some <$> elaborate origin[3]
  if residual.getNumArgs == 0 then return { fromObject }
  let node := residual[3]
  if node.getKind == ``escapeOpenContinuation then return { fromObject, openContinuation := true }
  return { fromObject, continuation := some (← elaborate node[0]) }

private def withReadout (theoremId arenaId : TSyntax `ident)
    (objectArena : Option (TSyntax `ident)) (term : TSyntax `term)
    (native : Bool) (origin residual : Syntax) (command : TSyntax `command) :
    CommandElabM Unit := registrationTransaction do
  let lawArena ← resolveArena arenaId
  let arenaName ← match objectArena with
    | none => pure lawArena
    | some id => resolveArena id
  let arena ← liftTermElabM <| resolveCanonicalArenaName arenaName
  let (descriptor, diagnostic) ← elaborateReadoutDescriptor term
  if (← get).messages.hasErrors then return
  let theoremName ← if native then declarationName theoremId else resolveTheorem theoremId
  let escapeInput ← elaborateEscapeInput origin residual
  TemplateBinding.withDeclaration { theoremName, arena, descriptor, diagnostic, escapeInput } <| elabCommand command

/-- Remove just the declared readout syntax node and dispatch the established
registration elaborator. All optional witnesses and their original syntax survive. -/
private def lowerReadout (stx : Syntax) (kind : Name) (start escapeStart : Nat) : TSyntax `command :=
  ⟨Syntax.node stx.getHeadInfo kind ((stx.getArgs.extract 0 start) ++
    stx.getArgs.extract (start + 5) escapeStart ++
    stx.getArgs.extract (escapeStart + 2) stx.getNumArgs)⟩

@[command_elab registerInformationTheoremReadoutCmd]
private def elabRegisteredReadout : CommandElab := fun stx =>
  withReadout ⟨stx[1]⟩ ⟨stx[3]⟩ none ⟨stx[7]⟩ false stx[15] stx[16]
    (lowerReadout stx ``registerInformationTheoremCmd 4 15)

@[command_elab registerInformationTheoremViaReadoutCmd]
private def elabReifierReadout : CommandElab := fun stx =>
  withReadout ⟨stx[1]⟩ ⟨stx[5]⟩ none ⟨stx[9]⟩ false stx[12] stx[13]
    (lowerReadout stx ``registerInformationTheoremViaCmd 6 12)

@[command_elab registerInformationTheoremOccurrenceReadoutCmd]
private def elabOccurrenceReadout : CommandElab := fun stx =>
  withReadout ⟨stx[1]⟩ ⟨stx[3]⟩ (some ⟨stx[5]⟩) ⟨stx[11]⟩ false stx[19] stx[20]
    (lowerReadout stx ``registerInformationTheoremOccurrenceCmd 8 19)

@[command_elab informationTheoremReadoutCmd]
private def elabNativeReadout : CommandElab := fun stx => do
  withReadout ⟨stx[1]⟩ ⟨stx[3]⟩ none ⟨stx[7]⟩ true stx[13] stx[14]
    (lowerReadout stx ``informationTheoremCmd 4 13)

@[command_elab informationTheoremOccurrenceReadoutCmd]
private def elabNativeOccurrenceReadout : CommandElab := fun stx =>
  withReadout ⟨stx[1]⟩ ⟨stx[3]⟩ (some ⟨stx[5]⟩) ⟨stx[11]⟩ true stx[17] stx[18]
    (lowerReadout stx ``informationTheoremOccurrenceCmd 8 17)

@[command_elab declareInformationTemplateBindingCmd]
private def elabBindingSidecar : CommandElab := fun stx => registrationTransaction do
  let lawArena ← resolveArena ⟨stx[3]⟩
  let explicitObject := stx[4].getNumArgs != 0
  let objectArena ← if explicitObject then resolveArena ⟨stx[4][1]⟩ else pure lawArena
  let arena ← liftTermElabM <| resolveCanonicalArenaName objectArena
  let (descriptor, diagnostic) ← elaborateReadoutDescriptor ⟨stx[8]⟩
  if (← get).messages.hasErrors then return
  let theoremName ← resolveTheorem ⟨stx[1]⟩
  let catalogId := if explicitObject then some (catalogIdFrom ⟨stx[4][3]⟩) else none
  TemplateBinding.declareSidecar theoremName arena catalogId descriptor diagnostic
    (← elaborateEscapeInput stx[10] stx[11])

end LeanInformationAudit
