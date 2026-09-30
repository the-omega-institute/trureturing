import LeanInformationAuditInterface.Store
import LeanInformationAuditInterface.OutputSyntax


namespace LeanInformationAudit

open Lean

/-- Command dispatch also considers identifiers, without reserving the spelling. -/
def expect_information_occurrenceKeyword : Parser.Parser := Parser.nonReservedSymbol "expect_information_occurrence" true
def information_theoremKeyword : Parser.Parser := Parser.nonReservedSymbol "information_theorem" true
def register_information_theoremKeyword : Parser.Parser := Parser.nonReservedSymbol "register_information_theorem" true
def register_information_templateKeyword : Parser.Parser := Parser.nonReservedSymbol "register_information_template" true
def informationInlineKeyword : Parser.Parser := Parser.nonReservedSymbol "inline" true

/-- Clause delimiters are tokens only while reading the preceding registration
term. They never enter an importing module's global identifier vocabulary. -/
def registrationTerm : Parser.Parser := {
  Parser.termParser with
  fn := Parser.adaptUncacheableContextFn (fun context =>
    { context with tokens := (#["realization", "variation", "sensitivity", "output_evidence", "escape"].foldl
        (fun tokens word => tokens.insert word word) context.tokens) }) Parser.termParser.fn }

@[combinator_formatter registrationTerm]
def registrationTermFormatter : PrettyPrinter.Formatter :=
  PrettyPrinter.Formatter.categoryParser.formatter `term
@[combinator_parenthesizer registrationTerm]
def registrationTermParenthesizer : PrettyPrinter.Parenthesizer :=
  PrettyPrinter.Parenthesizer.categoryParser.parenthesizer `term 0

declare_syntax_cat informationRealization
syntax (name := namedInformationRealization) ident : informationRealization
syntax (name := inlineInformationRealization) (priority := high)
  informationInlineKeyword registrationTerm " := " registrationTerm : informationRealization

/-- Preserve the group nodes inserted by the original combined `elab` forms. -/
-- Declare one independently expected auxiliary-root occurrence.
syntax (name := command___In__From_)
  group(expect_information_occurrenceKeyword) ident group(ppLine)
    &"in " ident group(ppLine)
    &"from " str : command

/-- Negative-fixture form for pinning an independently supplied statement identity. -/
syntax (name := command___In__From__Statement_id_)
  group(expect_information_occurrenceKeyword) ident group(ppLine)
    &"in " ident group(ppLine)
    &"from " str group(ppLine)
    &"statement_id " str : command

syntax (name := informationTheoremCmd)
  information_theoremKeyword ident ppLine
    &"in " ident ppLine
    &"primitives " registrationTerm ppLine
    (&"variation " ident)? (&"sensitivity " ident)?
    ": " term " := " term : command

syntax (name := registerInformationTheoremCmd)
  register_information_theoremKeyword ident ppLine
    &"in " ident ppLine
    &"primitives " registrationTerm &" realization " informationRealization
    (&" variation " ident)? (&" sensitivity " ident)? : command

syntax (name := registerInformationTheoremViaCmd)
  register_information_theoremKeyword ident &" via " term &" in " ident (&" output_evidence " term)? : command

syntax (name := informationTheoremOccurrenceCmd)
  information_theoremKeyword ident ppLine
    &"in " ident ppLine
    &"object_arena " ident ppLine
    &"catalog " ident ppLine
    &"primitives " registrationTerm ppLine
    (&"variation " ident)? (&"sensitivity " ident)?
    ": " term " := " term : command

syntax (name := registerInformationTheoremOccurrenceCmd)
  register_information_theoremKeyword ident ppLine
    &"in " ident ppLine
    &"object_arena " ident ppLine
    &"catalog " ident ppLine
    &"primitives " registrationTerm &" realization " informationRealization
    (&" variation " ident)? (&" sensitivity " ident)? : command

syntax (name := command__)
  group(register_information_templateKeyword) ident : command

syntax (name := «command__Constructors_[_,,]»)
  group(register_information_templateKeyword) ident &" constructors " num
    " [" ident,* "]" : command

declare_syntax_cat informationEscapeContinuation
syntax (name := escapeOpenContinuation) &"open" : informationEscapeContinuation
syntax (name := escapeCertifiedContinuation) term : informationEscapeContinuation

syntax (name := registerInformationTheoremReadoutCmd)
  register_information_theoremKeyword ident &" in " ident
  &"readout " &"via " "(" term ")" &" primitives " registrationTerm
  &" realization " informationRealization
  (&" variation " ident)? (&" sensitivity " ident)?
  (&" escape " &"from " "(" term ")")?
  (&" escape " &"continues " "(" informationEscapeContinuation ")")? : command

syntax (name := registerInformationTheoremViaReadoutCmd)
  register_information_theoremKeyword ident &" via " term &" in " ident
  &"readout " &"via " "(" term ")" (&" output_evidence " registrationTerm)?
  (&" escape " &"from " "(" term ")")?
  (&" escape " &"continues " "(" informationEscapeContinuation ")")? : command

syntax (name := registerInformationTheoremOccurrenceReadoutCmd)
  register_information_theoremKeyword ident &" in " ident &" object_arena " ident &" catalog " ident
  &"readout " &"via " "(" term ")" &" primitives " registrationTerm
  &" realization " informationRealization
  (&" variation " ident)? (&" sensitivity " ident)?
  (&" escape " &"from " "(" term ")")?
  (&" escape " &"continues " "(" informationEscapeContinuation ")")? : command

syntax (name := informationTheoremReadoutCmd)
  information_theoremKeyword ident &" in " ident &"readout " &"via " "(" term ")" &" primitives " registrationTerm
  (&" variation " ident)? (&" sensitivity " ident)?
  (&" escape " &"from " "(" term ")")?
  (&" escape " &"continues " "(" informationEscapeContinuation ")")? ": " term " := " term : command

syntax (name := informationTheoremOccurrenceReadoutCmd)
  information_theoremKeyword ident &" in " ident &" object_arena " ident &" catalog " ident
  &"readout " &"via " "(" term ")" &" primitives " registrationTerm
  (&" variation " ident)? (&" sensitivity " ident)?
  (&" escape " &"from " "(" term ")")?
  (&" escape " &"continues " "(" informationEscapeContinuation ")")? ": " term " := " term : command

/-- Source selections and obligations use the same enrollment and record pipeline. -/
syntax (name := registerInformationSourceTheoremCmd)
  register_information_theoremKeyword ident &" in " ident
  &"readout " &"via " "(" term ")" &" realizes " ident
  &" escape " &"from " &"source " "(" term ")"
  &" escape " &"continues " "(" informationEscapeContinuation ")" : command

/-- Retain a finite catalog while binding its exact Unit-family source audit. -/
syntax (name := registerInformationFiniteSourceTheoremCmd)
  register_information_theoremKeyword ident &" in " ident
  &"readout " &"via " "(" term ")" &" realizes " ident
  &" finite " &"via " ident &" variation " ident &" sensitivity " ident
  &" escape " &"from " &"source " "(" term ")"
  &" escape " &"continues " "(" informationEscapeContinuation ")" : command

end LeanInformationAudit



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
      type.isAppOf `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena ||
      type.isAppOf RegistrationElaboration.objectDomainArenaName ||
      type.isAppOf RegistrationElaboration.witnessArenaName then
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

private def primitiveRealizationId : Ident :=
  mkIdent `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization
private def theoremUnitId : Ident :=
  mkIdent `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
private def theoremUnitMkId : Ident :=
  mkIdent `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.mk
private def legacyToUnitId : Ident :=
  mkIdent `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit

/-- Name resolution only. Whether the resolved constant may be registered
(its kind, or a reserved judge-output name) is decided by the report. -/
private def resolveTheorem (id : TSyntax `ident) : CommandElabM Name := do
  try
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  catch _ =>
    throwErrorAt id
      "IE-C001 UnregisteredTheoremUnit: {← declarationName id}"

private def witnessName (id : Option (TSyntax `ident)) : CommandElabM Name := do
  match id with
  | none => return .anonymous
  | some id =>
    try liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    catch _ => declarationName id

private def optionalWitnessName (stx : Syntax) : CommandElabM Name := do
  if stx.getNumArgs != 2 then return .anonymous
  witnessName (some ⟨stx[1]⟩)

private def prepareRecordedEntry (rootId : Name) (entry : InformationRegistryEntry) :
    MetaM InformationRegistryEntry :=
  pure { entry with registrationModuleName := rootId }

private def requireClosedInput (value : Expr) : MetaM Unit := do
  if value.hasFVar || value.hasMVar || value.hasLooseBVars || value.hasLevelMVar then
    throwError "registration input contains unbound variables"

private def elaborateClosedTerm (inputSyntax : Syntax) : CommandElabM Expr := liftTermElabM do
  let value ← Term.elabTerm inputSyntax none
  Term.synthesizeSyntheticMVarsNoPostponing
  let value ← levelMVarToParam (← instantiateMVars value)
  requireClosedInput value
  return value

private def registerEntry (entry : InformationRegistryEntry)
    (suppliedPrimitives : Option Expr := none) (viaDescriptor : Option Expr := none)
    (outputEvidence : Option Expr := none) (realizationSource : Option Name := none) :
    CommandElabM Unit := do
  let input := TemplateBinding.currentDeclaration (← getEnv)
  let root := (← getEnv).header.mainModule
  let sourceText := (← read).fileMap.source
  let options ← getOptions
  modifyEnv fun env => RegistrationInputs.add env {
    entry := { entry with registrationModuleName := root },
    sourceText, options, suppliedPrimitives, viaDescriptor, outputEvidence, realizationSource,
    declaration := input }

private def catalogIdFrom (id : TSyntax `ident) : CatalogId :=
  let name := id.getId
  if (`_root_).isPrefixOf name then name.replacePrefix `_root_ .anonymous else name

private def resolveArena (id : TSyntax `ident) : CommandElabM Name := do
  try
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  catch _ =>
    throwErrorAt id "IE-C003 ArenaResolutionFailed: {id.getId}"

private def addExpectedOccurrence (theoremId arenaId : TSyntax `ident)
    (registrationModule statementIdentityOverride : String) : CommandElabM Unit := do
  let theoremName <- resolveTheorem theoremId
  let objectArenaName <- resolveArena arenaId
  let env <- getEnv
  let statementIdentity := statementIdentityOverride
  modifyEnv fun current => ExpectedOccurrenceManifest.addEntry current {
    rootId := env.header.mainModule
    objectArenaName
    theoremName
    statementIdentity
    capturedStatement := captureStatement env theoremName
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

/-- A supplied primitive bundle that does not elaborate against the bridge's
realization cannot match it; this is the registration's statement/proof mismatch. -/
private def elaboratePrimitives (theoremName : Name) (bridgeArena realization : Expr)
    (term : TSyntax `term) : CommandElabM Expr := do
  try
    liftTermElabM <| Term.withoutErrToSorry do
      -- The bundle is compiled at the arena's own state decidability, as the
      -- judge's primitive-bundle comparison does; no instance search is involved.
      let law := (← RegistrationElaboration.normalizeArena bridgeArena).law
      let arena ← mkAppM `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena #[law]
      let realizationType ← instantiateMVars (← whnfR (← inferType realization))
      unless realizationType.getAppArgs.size == 2 do throwError "realization argument mismatch"
      let compiler ← mkConstWithFreshMVarLevels
        `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle
      let bundle := mkAppN compiler #[
        ← mkAppM `D5.S3.ConceptDynamics.InformationEscape.Arena.State #[arena],
        realizationType.getAppArgs[1]!,
        ← mkAppM `D5.S3.ConceptDynamics.InformationEscape.Arena.stateDecidableEq #[arena],
        realization]
      let value ← elabTerm term (some (← inferType bundle))
      synthesizeSyntheticMVarsNoPostponing
      let value ← levelMVarToParam (← instantiateMVars value)
      requireClosedInput value
      return value
  catch error =>
    if error.isRuntime then throw error
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
        let arenaExpr ← mkConstWithFreshMVarLevels arenaName
        let arena := (← RegistrationElaboration.normalizeArena arenaExpr).law
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
    liftCoreM <| addAndCompile <| .thmDecl {
      name := realizationName, levelParams, type := expected, value := proof }
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

/-- Keep the theorem's universes rigid while the bridge's type determines their alignment. -/
private def alignedLegacyConstants (theoremName realizationName : Name) :
    TermElabM (Expr × Expr) := do
  let theoremInfo ← getConstInfo theoremName
  let theoremExpr := Lean.mkConst theoremName (theoremInfo.levelParams.map Level.param)
  let realization ← mkConstWithFreshMVarLevels realizationName
  let realizationType ← whnfR (← inferType realization)
  if realizationType.isAppOf
      `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization then
    unless ← isDefEq realizationType.getAppArgs[1]! (← inferType theoremExpr) do
      throwError "IE-C006 StatementProofMismatch: {theoremName}"
    let realization ← withLevelNames theoremInfo.levelParams <|
      levelMVarToParam (← instantiateMVars realization)
    if realization.hasLevelMVar then
      throwError "IE-C006 StatementProofMismatch: {theoremName}"
    return (realization, theoremExpr)
  return (realization, theoremExpr)

private def addLegacyUnit (theoremName realizationName unitName : Name) :
    CommandElabM Unit := do
  let env ← getEnv
  let unitExists := env.contains unitName
  let realizationExists := env.contains realizationName
  -- The recorder may see the same source theorem more than once (for example
  -- when an imported occurrence is explicitly re-registered).  Companion
  -- declarations are stable by design, so reuse a complete existing pair and
  -- leave duplicate policy to the report-time judge.  A half-created pair is
  -- still a malformed recorder state and cannot be safely reused.
  if unitExists then
    unless realizationExists do
      throwError "IE-C006 StatementProofMismatch: {theoremName}"
    return
  liftTermElabM do
    let (realization, theoremExpr) ← alignedLegacyConstants theoremName realizationName
    let realizationType ← whnfR (← inferType realization)
    unless realizationType.isAppOf
        `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization &&
        (← isDefEq realizationType.getAppArgs[1]! (← inferType theoremExpr)) do
      throwError "IE-C006 StatementProofMismatch: {theoremName}"
    let unit ← mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit
      #[realization, theoremExpr]
    let unitType ← inferType unit
    let unit ← levelMVarToParam (← instantiateMVars unit)
    let unitType ← levelMVarToParam (← instantiateMVars unitType)
    let levelParams :=
      (collectLevelParams (collectLevelParams {} unitType) unit).params.toList
    if unit.hasLevelMVar || unitType.hasLevelMVar then
      throwError "legacy unit retained a universe metavariable: {unitName}"
    let declaration := Declaration.defnDecl {
      name := unitName
      levelParams := levelParams
      type := unitType
      value := unit
      hints := .abbrev
      safety := .safe }
    let env ← getEnv
    let computationalInputs :=
      realizationType.getAppArgs[0]!.getUsedConstants ++
        realizationType.getAppArgs[2]!.getUsedConstants
    if computationalInputs.any (isNoncomputable env ·) then
      addDecl declaration
      modifyEnv (addNoncomputable · unitName)
    else
      addAndCompile declaration

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

/-- Elaborate one recorder-owned companion. The companion is well typed exactly
when the recorded inputs fit together; any elaboration error is reported as the
registration's own diagnostic rather than as an internal elaboration message. -/
private def elabCompanion (diagnostic : String) (command : TSyntax `command) :
    CommandElabM Unit := do
  let previous := (← get).messages
  modify fun s => { s with messages := {} }
  elabCommand command
  let produced := (← get).messages
  modify fun s => { s with messages := previous ++ (if produced.hasErrors then {} else produced) }
  if produced.hasErrors then throwError diagnostic

/-- A witness bridge's companion unit is built from its bridge at the registration
arena and from the positive half of its variation witness. -/
private def checkWitnessCompanionInputs (theoremName arenaName variationName : Name)
    (bridgeArena : Expr) : CommandElabM Unit := do
  let arenaMatches ← liftTermElabM do
    isDefEq bridgeArena (← mkConstWithFreshMVarLevels arenaName)
  unless arenaMatches do throwError "IE-C006 StatementProofMismatch: {theoremName}"
  if variationName.isAnonymous then
    throwError "unclassified_form:dtr.witness_bridge_requires_positive_variation"

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
    let entry ← liftTermElabM <| prepareRecordedEntry (← getEnv).header.mainModule {
      theoremName, unitName, arenaName, realizationName }
    let realizationId := absoluteIdentFrom theoremId realizationName
    elabCommand (← `(command| def $realizationId :
        $primitiveRealizationId:ident
          ($arenaId:ident).signature := $primitiveTerm))
    elabCommand (← `(command| theorem $theoremId : $statement := $proof))
    if (← get).messages.hasErrors then return
    let unitId := absoluteIdentFrom theoremId unitName
    elabCommand (← `(command| def $unitId :
        $theoremUnitId:ident ($arenaId:ident).toArena :=
      { primitives := ($realizationId:ident).toPrimitiveBundle
        Statement := $statement
        proof := $theoremId }))
    registerEntry { entry with
      variationWitness := ← optionalWitnessName stx[6]
      sensitivityWitness := ← optionalWitnessName stx[7]
    }

@[command_elab registerInformationTheoremViaCmd]
private def elabRegisterInformationTheoremVia : CommandElab := fun stx => registrationTransaction do
  -- The descriptor does not depend on the arena. Which arenas a derived
  -- bridge admits (law arena, rigid zero universes) is the report's P1 gate.
  let arenaName ← resolveArena ⟨stx[5]⟩
  let theoremName ← resolveTheorem ⟨stx[1]⟩
  let descriptor ← liftTermElabM do
    let value ← elabTerm stx[3] none
    synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    if value.hasMVar || value.hasLevelMVar then
      throwError "P1.UnresolvedMetavariables: {value}"
    requireClosedInput value
    return value
  let outputEvidence ← liftTermElabM do
    let arguments := descriptor.getAppArgs
    if arguments.size < 2 then return none
    let expected ← mkAppM `Nontrivial #[arguments[1]!]
    let value ← if stx[6].getNumArgs == 0 then synthInstance? expected
      else some <$> elabTerm stx[6][1] (some expected)
    synthesizeSyntheticMVarsNoPostponing
    value.mapM fun value => do
      let value ← instantiateMVars value
      requireClosedInput value
      return value
  let root := (← getEnv).header.mainModule
  let unitName := localCompanionName (← getEnv) root theoremName theoremUnitSuffix
  let realizationName := localCompanionName (← getEnv) root theoremName primitiveRealizationSuffix
  -- The reifier derives this bridge and unit from the recorded descriptor at
  -- report time; the recorder only fixes their names.
  registerEntry {
    theoremName, unitName, arenaName, realizationName, registrationModuleName := root } none (some descriptor) outputEvidence

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
      localCompanionName (← getEnv) (← getEnv).header.mainModule theoremName primitiveRealizationSuffix
    let (realizationName, isInline) ← resolveLegacyRealization theoremName arenaName
      generatedRealizationName realizationSyntax
    let unitName := localCompanionName (← getEnv) (← getEnv).header.mainModule theoremName theoremUnitSuffix
    let entry ← liftTermElabM <| prepareRecordedEntry (← getEnv).header.mainModule {
      theoremName, unitName, arenaName, realizationName }
    let realizationInfo ← match (← getEnv).find? realizationName with
    | some info => pure info
    | _ => throwError "IE-C006 StatementProofMismatch: {theoremName}"
    let (theoremType, realizationType) ← if isInline then
      pure ((← getConstInfo theoremName).type, realizationInfo.type)
    else liftTermElabM do
      let (realizationExpr, theoremExpr) ←
        alignedLegacyConstants theoremName realizationName
      return (← whnfR (← inferType theoremExpr), ← whnfR (← inferType realizationExpr))
    let legacyArgs := realizationType.getAppArgs
    unless (realizationType.getAppFn.constName? ==
        (some `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization) ||
        realizationType.getAppFn.constName? == some `D5.S3.ConceptDynamics.InformationEscape.EscapeRecord.EscapePrimitiveRealization ||
        realizationType.getAppFn.constName? == some RegistrationElaboration.witnessBridgeName) &&
        legacyArgs.size == 3 do
      throwError "IE-C006 StatementProofMismatch: {theoremName}"
    let suppliedPrimitives ← elaboratePrimitives theoremName legacyArgs[0]! legacyArgs[2]! primitiveTerm
    let variationName ← optionalWitnessName stx[8]
    let sensitivityName ← optionalWitnessName stx[9]
    if isInline then
      addLegacyUnit theoremName realizationName unitName
    else if realizationType.isAppOf
        `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization then
      addLegacyUnit theoremName realizationName unitName
    else
      let realizationId : TSyntax `ident := ⟨realizationSyntax.raw[0]⟩
      let unitId := absoluteIdentFrom theoremId (privateToUserName unitName)
      let unitType <- `(term|
        $theoremUnitId:ident ($arenaId:ident).toArena)
      let witnessUnitId := absoluteIdentFrom theoremId (RegistrationElaboration.witnessBridgeName.str "toTheoremUnit")
      let variationId := absoluteIdentFrom theoremId variationName
      let witness := realizationType.isAppOf RegistrationElaboration.witnessBridgeName
      if witness then
        checkWitnessCompanionInputs theoremName arenaName variationName legacyArgs[0]!
      let unitValue <- if witness then
          `(term| $witnessUnitId:ident
            $realizationId:ident (And.left $variationId:ident))
        else if realizationType.isAppOf `D5.S3.ConceptDynamics.InformationEscape.EscapeRecord.EscapePrimitiveRealization then
          `(term| { primitives := $primitiveTerm, Statement := _, proof := $theoremId:ident })
        else `(term|
          $legacyToUnitId:ident
            $realizationId:ident $theoremId:ident)
      let diagnostic := if witness then "unclassified_form:dtr.witness_bridge_requires_positive_variation"
        else s!"IE-C006 StatementProofMismatch: {theoremName}"
      if isPrivateName unitName then
        elabCompanion diagnostic (← `(command| private def $unitId : $unitType := $unitValue))
      else
        elabCompanion diagnostic (← `(command| def $unitId : $unitType := $unitValue))
    registerEntry { entry with
      variationWitness := ← optionalWitnessName stx[8]
      sensitivityWitness := ← optionalWitnessName stx[9]
    } (some suppliedPrimitives)

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
  let entry ← liftTermElabM <| prepareRecordedEntry (← getEnv).header.mainModule {
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
  let realizationId := absoluteIdentFrom theoremId realizationName
  elabCommand (← `(command| def $realizationId :
      $primitiveRealizationId:ident
        ($lawArenaId:ident).signature := $primitiveTerm))
  elabCommand (← `(command| theorem $theoremId : $statementTerm := $proofTerm))
  if (← get).messages.hasErrors then return
  let unitId := absoluteIdentFrom theoremId unitName
  let unitType <- `(term|
    $theoremUnitId:ident ($objectArenaId:ident))
  let unitValue <- `(term|
    $theoremUnitMkId:ident
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
  let entry ← liftTermElabM <| prepareRecordedEntry (← getEnv).header.mainModule {
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
  let (suppliedRealizationName, isInline) ← resolveLegacyRealization theoremName
    lawArenaName realizationName realizationSyntax
  let suppliedRealizationInfo <- match (← getEnv).find? suppliedRealizationName with
  | some info => pure info
  | _ => throwError "IE-C006 StatementProofMismatch: {theoremName}"
  let (theoremType, realizationType) ← if isInline then
    pure ((← getConstInfo theoremName).type, suppliedRealizationInfo.type)
  else liftTermElabM do
    let (realizationExpr, theoremExpr) ←
      alignedLegacyConstants theoremName suppliedRealizationName
    return (← whnfR (← inferType theoremExpr), ← whnfR (← inferType realizationExpr))
  let legacyArgs := realizationType.getAppArgs
  unless (realizationType.getAppFn.constName? ==
      (some `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization) ||
        realizationType.getAppFn.constName? == some `D5.S3.ConceptDynamics.InformationEscape.EscapeRecord.EscapePrimitiveRealization ||
        realizationType.getAppFn.constName? == some RegistrationElaboration.witnessBridgeName) &&
      legacyArgs.size == 3 do
    throwError "IE-C006 StatementProofMismatch: {theoremName}"
  let suppliedPrimitives ← elaboratePrimitives theoremName legacyArgs[0]! legacyArgs[2]! primitiveTerm
  let variationName ← optionalWitnessName stx[12]
  let sensitivityName ← optionalWitnessName stx[13]
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
    $theoremUnitId:ident $objectArenaId:ident)
  if isInline then
    addLegacyUnit theoremName realizationName unitName
  else if realizationType.isAppOf
      `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization then
    addLegacyUnit theoremName realizationName unitName
  else
    let qualifiedRealizationId := absoluteIdentFrom theoremId realizationName
    let witnessUnitId := absoluteIdentFrom theoremId (RegistrationElaboration.witnessBridgeName.str "toTheoremUnit")
    let variationId := absoluteIdentFrom theoremId variationName
    let witness := realizationType.isAppOf RegistrationElaboration.witnessBridgeName
    if witness then
      checkWitnessCompanionInputs theoremName lawArenaName variationName legacyArgs[0]!
    let unitValue <- if witness then
        `(term| $witnessUnitId:ident
          $qualifiedRealizationId:ident (And.left $variationId:ident))
      else if realizationType.isAppOf `D5.S3.ConceptDynamics.InformationEscape.EscapeRecord.EscapePrimitiveRealization then
        `(term| { primitives := $primitiveTerm, Statement := _, proof := $theoremId:ident })
      else `(term|
        $legacyToUnitId:ident
          $qualifiedRealizationId:ident $theoremId:ident)
    let diagnostic := if witness then "unclassified_form:dtr.witness_bridge_requires_positive_variation"
      else s!"IE-C006 StatementProofMismatch: {theoremName}"
    elabCompanion diagnostic (← `(command| def $unitId : $unitType := $unitValue))
  registerEntry { entry with
    variationWitness := ← optionalWitnessName stx[12]
    sensitivityWitness := ← optionalWitnessName stx[13]
  } (some suppliedPrimitives) (realizationSource := some suppliedRealizationName)

end LeanInformationAudit

namespace LeanInformationAudit
open Lean Elab Command

private def elaborateTemplateEnrollment (id : TSyntax `ident)
    (version : Nat) (types : Array (TSyntax `ident)) : CommandElabM Unit := do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let constructors ← types.mapM fun ast => liftCoreM <| realizeGlobalConstNoOverloadWithInfo ast
  let owner := (← getEnv).header.mainModule
  let options ← getOptions
  let sourceText := (← read).fileMap.source
  modifyEnv fun env => TemplateEnrollmentInputs.add env {
    owner, name, version, constructors, options, sourceText }

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
  let arena := arenaName
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

end LeanInformationAudit

namespace LeanInformationAudit
open Lean Meta Elab Command

@[command_elab registerInformationSourceTheoremCmd]
private def elabSourceRegistration : CommandElab := fun stx => registrationTransaction do
  let theoremName ← resolveTheorem ⟨stx[1]⟩
  let arenaName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[3]
  let recordName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[10]
  let selection ← liftTermElabM do
    let value ← Term.elabTermEnsuringType stx[15] (mkConst ``SourceSelection)
    Term.synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    if value.hasMVar then throwError "unclassified_form:source.selection_open"
    -- Syntax transport is evaluated, never a mathematical proposition or readout.
    unsafe evalExpr SourceSelection (mkConst ``SourceSelection) value
  let (descriptor, diagnostic) ← elaborateReadoutDescriptor ⟨stx[7]⟩
  let residual ← if stx[20].getKind == ``escapeOpenContinuation then
      pure ({ openContinuation := true } : EscapeRecordInput)
    else do
      let value ← elaborateClosedTerm stx[20][0]
      pure ({ continuation := some value } : EscapeRecordInput)
  let info ← getConstInfo recordName
  let source ← getConstInfo theoremName
  let descriptor := descriptor.map (fun e => e.instantiateLevelParams info.levelParams
    (source.levelParams.map Level.param))
  let root := (← getEnv).header.mainModule
  let unit := catalogQualifiedName root arenaName .anonymous theoremName theoremUnitSuffix
  let unitDecl : Declaration := .defnDecl {
    name := unit, levelParams := info.levelParams, type := info.type,
    value := mkConst recordName (info.levelParams.map Level.param), hints := .abbrev, safety := .safe }
  if isNoncomputable (← getEnv) recordName then
    -- Retaining a mathematical record does not make its readout executable.
    -- addDecl still sends the unchanged declaration through the kernel.
    liftCoreM <| addDecl unitDecl
    modifyEnv (addNoncomputable · unit)
  else
    liftCoreM <| addAndCompile unitDecl
  TemplateBinding.withDeclaration {
    theoremName, arena := arenaName, descriptor, diagnostic,
    escapeInput := { residual with sourceSelection := some selection } } do
    registerEntry {
      theoremName, unitName := unit, arenaName, realizationName := recordName,
      sourceBound := true, objectArenaName := arenaName, resolvedArenaName := arenaName,
      registrationModuleName := root, localRegistrationNames := false }

end LeanInformationAudit

namespace LeanInformationAudit
open Lean Meta Elab Command

@[command_elab registerInformationFiniteSourceTheoremCmd]
private def elabFiniteSourceRegistration : CommandElab := fun stx => registrationTransaction do
  let `(command| register_information_theorem $theoremId:ident in $arenaId:ident
      readout via ($descriptorSyntax:term) realizes $recordId:ident
      finite via $bridgeId:ident variation $variationId:ident sensitivity $sensitivityId:ident
      escape from source ($selectionSyntax:term) escape continues ($continuation:informationEscapeContinuation)) := stx
    | throwUnsupportedSyntax
  let residual ← if continuation.raw.getKind == ``escapeOpenContinuation then
      pure ({ openContinuation := true } : EscapeRecordInput)
    else do
      let value ← elaborateClosedTerm continuation.raw[0]
      pure ({ continuation := some value } : EscapeRecordInput)
  let theoremName ← resolveTheorem theoremId
  let arenaName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo arenaId
  let recordName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo recordId
  let bridgeName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo bridgeId
  let selection ← liftTermElabM do
    let value ← Term.elabTermEnsuringType selectionSyntax (mkConst ``SourceSelection)
    Term.synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    if value.hasMVar then throwError "unclassified_form:source.selection_open"
    unsafe evalExpr SourceSelection (mkConst ``SourceSelection) value
  let (descriptor, diagnostic) ← elaborateReadoutDescriptor descriptorSyntax
  let bridgeType := (← getConstInfo bridgeName).type
  unless bridgeType.isAppOfArity
      `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization 3 do
    throwError "unclassified_form:source.finite_bridge"
  let actualSyntax ← liftTermElabM <| PrettyPrinter.delab bridgeType.getAppArgs[2]!
  let bridgeSyntax ← `(informationRealization| $bridgeId:ident)
  TemplateBinding.withDeclaration {
    theoremName, arena := arenaName, descriptor, diagnostic
    sourceRecord := some recordName
    escapeInput := { residual with
      sourceSelection := some selection
      finiteBridge := some bridgeName } } do
    elabCommand (← `(command| register_information_theorem $theoremId in $arenaId
      primitives ($actualSyntax).toPrimitiveBundle realization $bridgeSyntax
      variation $variationId sensitivity $sensitivityId))

end LeanInformationAudit

namespace LeanInformationAudit
open Lean Elab Command

@[command_elab sealInformationTheoryCmd]
private def recordSeal : CommandElab := fun _ => do
  let rootId := (← getEnv).header.mainModule
  let options ← getOptions
  modifyEnv fun env => SealInputs.add env { rootId, options }

end LeanInformationAudit
