import LeanInformationAuditInterface.Store
import Lake.Build.Trace
import Lean.Util.CollectLevelMVars
import Lean.Util.ReplaceLevel

namespace LeanInformationAudit.RegMigration

open Lean Meta Elab Command

private def namesJson (names : List Name) : Json :=
  Json.arr (names.toArray.map fun name => Json.str name.toString)

private def nameText (name : Name) : String :=
  if name.isAnonymous then "" else name.toString

private def nameComponents : Name → Array Json
  | .anonymous => #[]
  | .str parent word => nameComponents parent |>.push (Json.str word)
  | .num parent value => nameComponents parent |>.push (toJson value)

private def nameComponentsMap (names : List (String × Name)) : Json :=
  Json.mkObj (names.map fun (key, name) => (key, Json.arr (nameComponents name)))

private def withMetaInputContext (label : String) (action : MetaM α) : MetaM α :=
  withCurrHeartbeats <| tryCatchRuntimeEx action fun error => withCurrHeartbeats do
    let message ← addMessageContextFull error.toMessageData
    throw <| Exception.error Syntax.missing m!"RM-INPUT-ROW: {label}: {message}"

private def optionJson (options : Options) : CoreM Json := do
  let mut settings : Array (Name × DataValue) := #[]
  for setting in options do settings := settings.push setting
  settings := settings.qsort (fun left right => left.1.toString < right.1.toString)
  let mut result := #[]
  for (name, value) in settings do
    let (kind, encoded) ← match value with
      | .ofBool value => pure ("bool", Json.bool value)
      | .ofNat value => pure ("nat", toJson value)
      | .ofInt value => pure ("int", toJson value)
      | .ofString value => pure ("string", Json.str value)
      | .ofName value => pure ("name", Json.str value.toString)
      | .ofSyntax _ => throwError "RM-INPUT-OPTION-TYPE: {name}: syntax"
    result := result.push <| Json.mkObj [
      ("name", Json.str name.toString), ("name_components", Json.arr (nameComponents name)),
      ("type", Json.str kind), ("value", encoded),
      ("value_components", match value with
        | .ofName name => Json.arr (nameComponents name)
        | _ => Json.null)]
  return Json.arr result

private def printOptions : Options :=
  ({} : Options) |>.setBool `pp.all true |>.setBool `pp.fullNames true
    |>.setBool `pp.privateNames false
    |>.setBool `pp.universes true |>.setBool `pp.explicit true
    |>.setBool `pp.notation false |>.setBool `pp.proofs true
    |>.set `pp.maxDepth (100000 : Nat) |>.set `pp.maxSteps (1000000 : Nat)
    |>.set `maxRecDepth (20000 : Nat)

mutual
  private partial def openPrintedSyntax? (stx : Syntax) : Option Syntax :=
    if stx.isMissing || stx.isOfKind ``Parser.Term.hole ||
        stx.isOfKind ``Parser.Term.syntheticHole || stx.isOfKind ``Parser.Term.omission then
      some stx
    else if stx.isOfKind ``Parser.Term.basicFun then
      openPrintedBinderSyntax? stx[0] <|>
        (stx.getArgs.extract 1 stx.getArgs.size).findSome? openPrintedSyntax?
    else if stx.isOfKind ``Parser.Term.forall then
      openPrintedBinderSyntax? stx[1] <|>
        ((stx.getArgs.extract 2 stx.getArgs.size).findSome? openPrintedSyntax?)
    else if stx.isOfKind ``Parser.Term.depArrow then
      openPrintedBinderSyntax? stx[0] <|>
        (stx.getArgs.extract 1 stx.getArgs.size).findSome? openPrintedSyntax?
    else stx.getArgs.findSome? openPrintedSyntax?

  /-- Anonymous binder identifiers are names, while their annotations remain terms. -/
  private partial def openPrintedBinderSyntax? (stx : Syntax) : Option Syntax :=
    if stx.isOfKind ``Parser.Term.hole then none
    else if stx.isOfKind ``Parser.Term.paren then
      openPrintedBinderSyntax? stx[1]
    else if stx.isOfKind ``Parser.Term.typeAscription ||
        stx.isOfKind ``Parser.Term.explicitBinder || stx.isOfKind ``Parser.Term.implicitBinder ||
        stx.isOfKind ``Parser.Term.strictImplicitBinder then
      openPrintedBinderSyntax? stx[1] <|>
        (stx.getArgs.extract 2 stx.getArgs.size).findSome? openPrintedSyntax?
    else if stx.getKind == nullKind || stx.isOfKind ``Parser.Term.app then
      stx.getArgs.findSome? openPrintedBinderSyntax?
    else openPrintedSyntax? stx
end

/-- A fallback is syntax, with explicit levels and names, never Expr.toString. -/
private def expressionJson (label : String) (expression : Expr) : MetaM Json := do
  if expression.hasFVar || expression.hasMVar || expression.hasLooseBVars ||
      expression.hasLevelMVar then
    throwError "RM-INPUT-OPEN-EXPRESSION: {label}"
  let text ← try
      withOptions (fun _ => printOptions) do
        return (← PrettyPrinter.ppExpr expression).pretty 100000
    catch _ => throwError "RM-INPUT-PRINT: {label}"
  match Parser.runParserCategory (← getEnv) `term text with
  | .error error => throwError "RM-INPUT-PRINT-SYNTAX: {label}: {error}: {text.take 1200}"
  | .ok stx =>
    if let some openStx := openPrintedSyntax? stx then
      throwError "RM-INPUT-OPEN-PRINTED-SYNTAX: {label}: {openStx.getKind}: {text.take 1200}"
  return Json.mkObj [
    ("text", Json.str text), ("printed", Json.bool true),
    ("level_params", namesJson (collectLevelParams {} expression).params.toList)]

private def optionalExpressionJson (label : String) (expression : Option Expr) : MetaM Json :=
  match expression with
  | none => pure Json.null
  | some expression => expressionJson label expression

private def sourceSelectionJson (selection : SourceSelection) : Json :=
  Json.mkObj [
    ("owner", Json.str selection.owner.toString),
    ("name_components", nameComponentsMap [("owner", selection.owner)]),
    ("definition", match selection.definition with
      | none => Json.null
      | some definition => Json.mkObj [
          ("owner", Json.str definition.owner.toString),
          ("name", Json.str definition.name.toString),
          ("name_components", nameComponentsMap [
            ("owner", definition.owner), ("name", definition.name)]),
          ("path", toJson definition.path)]),
    ("coordinates", toJson selection.coordinates),
    ("readouts", Json.arr (selection.readouts.map fun readout => Json.mkObj [
      ("path", toJson readout.path), ("stateBinder", toJson readout.stateBinder),
      ("functionOperand", Json.bool readout.functionOperand),
      ("stateOperand", toJson readout.stateOperand),
      ("booleanPredicate", Json.bool readout.booleanPredicate)]))]

private def constantExpression (name : Name) (levels : List Name) : MetaM Expr := do
  unless (← getEnv).contains name do throwError "RM-INPUT-MISSING-CONSTANT: {name}"
  let info ← getConstInfo name
  return mkConst name <| (if info.levelParams.length == levels.length then levels
    else info.levelParams).map Level.param

private def alignedBridgeExpression (name : Name) (target : ConstantInfo)
    (sourceArena : Option Expr := none) : TermElabM Expr :=
  Term.withLevelNames target.levelParams do
    let expression ← mkConstWithFreshMVarLevels name
    let type ← whnf (← inferType expression)
    if let some sourceArena := sourceArena then
      unless type.isAppOf `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration do
        throwError "RM-INPUT-SOURCE-BRIDGE-SHAPE: {name}"
      let some arena := type.getAppArgs[0]? | throwError "RM-INPUT-SOURCE-BRIDGE-ARENA: {name}"
      unless ← isDefEq arena sourceArena do throwError "RM-INPUT-SOURCE-BRIDGE-ARENA: {name}"
    else
      unless type.isAppOf `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization do
        let some statement := type.getAppArgs[1]? | throwError "RM-INPUT-BRIDGE-SHAPE: {name}"
        unless ← isDefEq statement target.type do throwError "RM-INPUT-BRIDGE-TARGET: {name}"
    Term.levelMVarToParam (← instantiateMVars expression)

private def alignedArenaExpression (name : Name) (expected : Expr)
    (levels : List Name) : TermElabM Expr := Term.withLevelNames levels do
  let expression ← mkConstWithFreshMVarLevels name
  let type ← whnf (← inferType expression)
  let comparison ← if type.isConstOf RegistrationElaboration.objectDomainArenaName then
      pure (← RegistrationElaboration.normalizeArena expression).law
    else pure expression
  unless ← isDefEq comparison expected do throwError "RM-INPUT-ARENA-ALIGNMENT: {name}"
  Term.levelMVarToParam (← instantiateMVars expression)

private def sortLevel (expression : Expr) : MetaM Level := do
  let type ← whnf (← inferType expression)
  let .sort level := type | throwError "RM-INPUT-NON-TYPE"
  return level

private def typeLevel (expression : Expr) : MetaM Level := do
  match (← sortLevel expression).normalize.dec with
  | some level => return level
  | none => throwError "RM-INPUT-NON-TYPE-UNIVERSE"

private def levelText (level : Level) : String :=
  toString level

private def closedLevelsJson (label : String) (levels : Array Level) : MetaM Json := do
  if levels.any (·.hasMVar) then throwError "RM-INPUT-OPEN-UNIVERSE: {label}"
  return toJson (levels.map levelText)

private def sourceBacked (slots : Json) (name : String) : Bool :=
  (slots.getObjVal? name).isOk

private def fallbackExpressionJson (slots : Json) (slot label : String)
    (expression : Option Expr) : MetaM Json :=
  if sourceBacked slots slot then pure Json.null else optionalExpressionJson label expression

private def jsonName (value : Json) : MetaM Name := do
  let components ← Lean.ofExcept <| value.getArr?
  components.foldlM (init := Name.anonymous) fun name component =>
    match component.getStr? with
    | .ok word => pure (name.str word)
    | .error _ => do
      let number ← Lean.ofExcept <| component.getNat?
      pure (name.num number)

private partial def expressionConstants (expression : Expr) : Array (Name × List Level) :=
  match expression with
  | .const name levels => #[(name, levels)]
  | .app function argument => expressionConstants function ++ expressionConstants argument
  | .lam _ type body _ | .forallE _ type body _ =>
      expressionConstants type ++ expressionConstants body
  | .letE _ type value body _ =>
      expressionConstants type ++ expressionConstants value ++ expressionConstants body
  | .mdata _ body | .proj _ _ body => expressionConstants body
  | _ => #[]

private partial def sourceLevel (value : Json) : MetaM Level := do
  let kind ← Lean.ofExcept <| value.getObjValAs? String "kind"
  match kind with
  | "param" => return .param (← jsonName (← Lean.ofExcept <| value.getObjVal? "name_components"))
  | "nat" => return Level.ofNat (← Lean.ofExcept <| value.getObjValAs? Nat "value")
  | "add" =>
      let left ← sourceLevel (← Lean.ofExcept <| value.getObjVal? "left")
      return left.addOffset (← Lean.ofExcept <| value.getObjValAs? Nat "offset")
  | "max" | "imax" =>
      let args ← Lean.ofExcept <| value.getObjValAs? (Array Json) "args"
      unless args.size >= 2 do throwError "RM-INPUT-SOURCE-UNIVERSE-SHAPE: {kind}"
      let levels ← args.mapM sourceLevel
      return (levels.extract 0 (levels.size - 1)).foldr
        (if kind == "max" then mkLevelMax else mkLevelIMax) levels.back!
  | _ => throwError "RM-INPUT-SOURCE-UNIVERSE-UNRESOLVED: {kind}"

private partial def compositeSourceLevel : Level → Bool
  | .max _ _ | .imax _ _ => true
  | .succ level => compositeSourceLevel level
  | _ => false

private partial def substituteSourceLevel (slot : String) (source : Level)
    (mapping : NameMap Level) : MetaM Level := do
  match source with
  | .param name =>
      let some captured := mapping.find? name
        | throwError "RM-INPUT-SOURCE-UNIVERSE-AMBIGUOUS: {slot}: {name}"
      return captured
  | .zero => return .zero
  | .succ level => return .succ (← substituteSourceLevel slot level mapping)
  | .max left right =>
      return mkLevelMax (← substituteSourceLevel slot left mapping)
        (← substituteSourceLevel slot right mapping)
  | .imax left right =>
      return mkLevelIMax (← substituteSourceLevel slot left mapping)
        (← substituteSourceLevel slot right mapping)
  | .mvar _ => throwError "RM-INPUT-SOURCE-UNIVERSE-OPEN: {slot}"

private partial def matchSourceLevel (slot : String) (source captured : Level)
    (mapping : NameMap Level) : MetaM (NameMap Level) := do
  if captured.hasMVar then throwError "RM-INPUT-SOURCE-UNIVERSE-OPEN: {slot}"
  match source with
  | .param name =>
      if let some prior := mapping.find? name then
        unless prior.normalize == captured.normalize do
          throwError "RM-INPUT-SOURCE-UNIVERSE-AMBIGUOUS: {slot}: {name}"
      return mapping.insert name captured
  | .zero =>
      unless captured.normalize == .zero do
        throwError "RM-INPUT-SOURCE-UNIVERSE-UNRESOLVED: {slot}: zero"
      return mapping
  | .succ predecessor =>
      let some predecessorCaptured := captured.normalize.dec
        | throwError "RM-INPUT-SOURCE-UNIVERSE-UNRESOLVED: {slot}: successor"
      matchSourceLevel slot predecessor predecessorCaptured mapping
  | .max _ _ | .imax _ _ =>
      let instantiated ← substituteSourceLevel slot source mapping
      unless instantiated.normalize == captured.normalize do
        throwError "RM-INPUT-SOURCE-UNIVERSE-UNRESOLVED: {slot}: composite"
      return mapping
  | .mvar _ => throwError "RM-INPUT-SOURCE-UNIVERSE-OPEN: {slot}"

/-- Source syntax survives; its constant universe applications and universe parameter
annotations use the levels retained in the compiled input. No source term is elaborated here. -/
private def sourceSpecializations (context slots : Json) (terms : Array (String × Expr)) :
    MetaM Json := do
  let ns ← jsonName (← Lean.ofExcept <| context.getObjVal? "namespace_components")
  let mut opens : List OpenDecl := []
  for entry in (← Lean.ofExcept <| context.getObjValAs? (Array Json) "open_decls") do
    let kind ← Lean.ofExcept <| entry.getObjValAs? String "kind"
    if kind == "simple" then
      let name ← jsonName (← Lean.ofExcept <| entry.getObjVal? "namespace_components")
      opens := opens.concat (.simple name [])
    else if kind == "explicit" then
      let name ← jsonName (← Lean.ofExcept <| entry.getObjVal? "name_components")
      let declaration ← jsonName (← Lean.ofExcept <| entry.getObjVal? "declaration_components")
      opens := opens.concat (.explicit name declaration)
    else throwError "RM-INPUT-SOURCE-OPEN-KIND: {kind}"
  let env ← getEnv
  let mut result : List (String × Json) := []
  for (slot, expression) in terms do
    let .ok slotSyntax := slots.getObjVal? slot | continue
    let constants := expressionConstants expression
    let mut specializations := #[]
    let mut sourceMapping : NameMap Level := {}
    let mut compositeConstraints : Array (Level × Level) := #[]
    for identifier in (← Lean.ofExcept <| slotSyntax.getObjValAs? (Array Json) "identifiers") do
      let name ← jsonName (← Lean.ofExcept <| identifier.getObjVal? "name_components")
      let resolutions := ResolveName.resolveGlobalName env {} ns opens name
      let candidates := constants.filter fun (constant, _) =>
        resolutions.any fun (resolved, projections) => resolved == constant && projections.isEmpty
      let candidates := candidates.foldl (init := #[]) fun found candidate =>
        if found.contains candidate then found else found.push candidate
      if candidates.size > 1 then
        throwError "RM-INPUT-SOURCE-UNIVERSE-AMBIGUOUS: {slot}: {name}"
      let some (_, levels) := candidates[0]? | continue
      if levels.isEmpty then continue
      if levels.any (·.hasMVar) then
        if (identifier.getObjValAs? Bool "explicit_universes").toOption == some true then
          throwError "RM-INPUT-SOURCE-UNIVERSE-OPEN: {slot}: {name}"
        continue
      if (identifier.getObjValAs? Bool "explicit_universes").toOption == some true then
        let sourceLevels ← Lean.ofExcept <| identifier.getObjValAs? (Array Json) "source_levels"
        unless sourceLevels.size == levels.length do
          throwError "RM-INPUT-SOURCE-UNIVERSE-SHAPE: {slot}: {name}"
        for (source, captured) in sourceLevels.toList.zip levels do
          let source ← sourceLevel source
          if compositeSourceLevel source then
            compositeConstraints := compositeConstraints.push (source, captured)
          else sourceMapping ← matchSourceLevel slot source captured sourceMapping
      let head ← Lean.ofExcept <| identifier.getObjValAs? String "head_text"
      let text ← Lean.ofExcept <| identifier.getObjValAs? String "text"
      let term := head ++ ".{" ++ String.intercalate ", " (levels.map levelText) ++ "}"
      if term == text then continue
      let usedLevels := levels.foldl (fun used level => collectLevelParams used (.sort level)) {}
      specializations := specializations.push <| Json.mkObj [
        ("start", ← Lean.ofExcept <| identifier.getObjVal? "start"),
        ("end", ← Lean.ofExcept <| identifier.getObjVal? "end"),
        ("text", Json.str text), ("term", Json.str term),
        ("levels", toJson (levels.map levelText)),
        ("level_params", namesJson usedLevels.params.toList)]
    for (source, captured) in compositeConstraints do
      sourceMapping ← matchSourceLevel slot source captured sourceMapping
    for occurrence in (← Lean.ofExcept <| slotSyntax.getObjValAs? (Array Json) "universe_occurrences") do
      let start ← Lean.ofExcept <| occurrence.getObjValAs? Nat "start"
      let stop ← Lean.ofExcept <| occurrence.getObjValAs? Nat "end"
      if specializations.any (fun entry =>
          (entry.getObjValAs? Nat "start").toOption.getD stop <= start &&
          stop <= (entry.getObjValAs? Nat "end").toOption.getD start) then continue
      let name ← jsonName (← Lean.ofExcept <| occurrence.getObjVal? "name_components")
      let captured ← match sourceMapping.find? name with
        | some level => pure level
        | none =>
            if (collectLevelParams {} expression).params.contains name then pure (.param name)
            else throwError "RM-INPUT-SOURCE-UNIVERSE-UNRESOLVED: {slot}: {name}"
      let text ← Lean.ofExcept <| occurrence.getObjValAs? String "text"
      let level := levelText captured
      if level == text then continue
      specializations := specializations.push <| Json.mkObj [
        ("kind", Json.str "universe-parameter"), ("start", toJson start), ("end", toJson stop),
        ("text", Json.str text), ("term", Json.str ("(" ++ level ++ ")")),
        ("levels", toJson [level]),
        ("level_params", namesJson (collectLevelParams {} (.sort captured)).params.toList)]
    if !specializations.isEmpty then result := result.concat (slot, Json.arr specializations)
  return Json.mkObj result

private def freshenCapturedUniverses (expression : Expr) : MetaM Expr := do
  let mut replacements : NameMap Level := {}
  for metaVariable in (collectLevelMVars {} expression).result do
    replacements := replacements.insert metaVariable.name (← mkFreshLevelMVar)
  return expression.replaceLevel fun
    | .mvar metaVariable => replacements.find? metaVariable.name
    | _ => none

private def registrationJson (owner : Name) (index : Nat) (input : RegistrationInput)
    (context slots : Json) :
    TermElabM Json := do
  let entry := input.entry
  let target ← getConstInfo entry.theoremName
  let levels := target.levelParams
  let provisionalArena ← constantExpression entry.arenaName levels
  let bridge ← if (← getEnv).contains (input.realizationSource.getD entry.realizationName) then
      alignedBridgeExpression (input.realizationSource.getD entry.realizationName) target
        (if entry.sourceBound then some provisionalArena else none)
    else match input.viaDescriptor with
      | some descriptor => pure descriptor
      | none => throwError "RM-INPUT-MISSING-BRIDGE: {owner}: {entry.theoremName}"
  let bridgeType ← whnf (← inferType bridge)
  let sourceTargetMatches : Option Bool ← if entry.sourceBound then do
      let some statement := bridgeType.getAppArgs[1]?
        | throwError "RM-INPUT-SOURCE-BRIDGE-SHAPE: {entry.realizationName}"
      let sourceMatches ← liftM <| (Lean.withoutModifyingState
        (isDefEq statement target.type) : MetaM Bool)
      pure (some sourceMatches)
    else pure none
  let generated := bridgeType.isAppOf
    `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization
  let expectedArena := if generated then provisionalArena else bridgeType.getAppArgs[0]?.getD provisionalArena
  let arena ← if generated then pure provisionalArena else alignedArenaExpression entry.arenaName expectedArena levels
  let objectArena ← if entry.objectArenaName.isAnonymous || entry.objectArenaName == entry.arenaName then
      pure arena else constantExpression entry.objectArenaName levels
  let arenaType ← whnf (← inferType arena)
  let bridgeKind := if entry.sourceBound then "source"
    else if arenaType.isConstOf RegistrationElaboration.witnessArenaName then "witness"
    else if bridgeType.isAppOf
      `D5.S3.ConceptDynamics.InformationEscape.EscapeRecord.EscapePrimitiveRealization then "forward"
    else "legacy"
  let actual := if generated then some bridge else if bridgeKind == "source" then none
    else bridgeType.getAppArgs[2]?
  let suppliedPrimitives : Option Expr ← match input.suppliedPrimitives, input.viaDescriptor, actual with
    | none, some _, some actual => do
      let law := (← RegistrationElaboration.normalizeArena arena).law
      let object ← mkAppM `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena #[law]
      let state ← mkAppM `D5.S3.ConceptDynamics.InformationEscape.Arena.State #[object]
      let decidable ← mkAppM `D5.S3.ConceptDynamics.InformationEscape.Arena.stateDecidableEq #[object]
      let signature := (← whnf (← inferType actual)).getAppArgs[1]!
      let value ← mkAppOptM `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle
        #[some state, some signature, some decidable, some actual]
      pure (some (← instantiateMVars value))
    | _, _, _ => pure input.suppliedPrimitives
  let declaration := input.declaration
  let descriptor ← match declaration.bind (·.descriptor) with
    | none => pure none
    | some descriptor => do
        let descriptor ← if descriptor.hasLevelMVar then freshenCapturedUniverses descriptor
          else pure descriptor
        let descriptor ← instantiateMVars descriptor
        if bridgeKind == "source" && descriptor.hasLevelMVar then
          let sourceActual := mkProj
            `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration 0 bridge
          let expectedType ← inferType sourceActual
          unless ← isDefEq (← inferType descriptor) expectedType do
            throwError "RM-INPUT-SOURCE-READOUT-ALIGNMENT: {entry.theoremName}"
        pure (some (← instantiateMVars descriptor))
  let escape := declaration.map (·.escapeInput) |>.getD {}
  let family ← match declaration.bind (·.sourceRecord) with
    | none => pure none
    | some name => some <$> constantExpression name levels
  let variation ← if entry.variationWitness.isAnonymous then pure none
    else some <$> constantExpression entry.variationWitness levels
  let sensitivity ← if entry.sensitivityWitness.isAnonymous then pure none
    else some <$> constantExpression entry.sensitivityWitness levels
  let fallback := mkConst ``Unit
  let typeFor (value : Option Expr) : MetaM Expr :=
    match value with | none => pure fallback | some value => inferType value
  let typeActions : Array (MetaM Expr) := #[pure arenaType, inferType objectArena, typeFor descriptor,
      typeFor variation, typeFor sensitivity, typeFor escape.fromObject,
      typeFor escape.continuation, typeFor family]
  let typeArgs ← typeActions.mapM fun action => (liftM action : TermElabM Expr)
  let argumentLevels ← typeArgs.mapIdxM fun index type =>
    if index == 2 || index == 5 then typeLevel type else sortLevel type
  let mut implementationLevels := Array.replicate 9 Level.zero
  let bridgeArena ← if generated then do
      pure (← RegistrationElaboration.normalizeArena arena).law
    else pure (bridgeType.getAppArgs[0]?.getD arena)
  let sourceArenaIsObjectDomain := arenaType.isConstOf RegistrationElaboration.objectDomainArenaName
  let bridgeArenaType ← whnf (← inferType bridgeArena)
  let originalArenaType ← whnfR (← inferType provisionalArena)
  let sourceBridgeTypesAlign ← liftM <| (Lean.withoutModifyingState
    (isDefEq originalArenaType bridgeArenaType) : MetaM Bool)
  let bridgeArenaFromSource := !sourceArenaIsObjectDomain && sourceBridgeTypesAlign &&
    bridgeArena.consumeMData == arena.consumeMData &&
    bridgeArena.consumeMData == provisionalArena.consumeMData
  let arenaLevels := bridgeArenaType.getAppFn.constLevels!
  if bridgeKind == "source" then
    unless arenaLevels.length == 5 do throwError "RM-INPUT-SOURCE-UNIVERSES: {entry.theoremName}"
    for (level, index) in arenaLevels.zipIdx do
      implementationLevels := implementationLevels.set! (index + 3) level
  else if bridgeKind == "witness" then
    unless arenaLevels.length == 1 do throwError "RM-INPUT-WITNESS-UNIVERSES: {entry.theoremName}"
    implementationLevels := implementationLevels.set! 8 arenaLevels.head!
  else
    unless arenaLevels.length == 3 do throwError "RM-INPUT-BRIDGE-UNIVERSES: {entry.theoremName}"
    for (level, index) in arenaLevels.zipIdx do
      implementationLevels := implementationLevels.set! index level
  let sourceTerms : Array (Option Expr) := #[some arena, some objectArena, descriptor,
    variation, sensitivity, escape.fromObject, escape.continuation, family]
  let objectArenaSlot := if objectArena.consumeMData == arena.consumeMData &&
      sourceBacked slots "arena" then "arena" else "object_arena"
  let typeSlotNames := #["arena", objectArenaSlot, "readout", "variation", "sensitivity",
    "escape_from", "continuation", "source_record"]
  let typeArgSourceSlots := sourceTerms.mapIdx fun index term =>
    if term.isSome && sourceBacked slots typeSlotNames[index]! then some typeSlotNames[index]!
    else none
  let specializedTerms := (#[
    ("arena", some arena), ("object_arena", some objectArena), ("readout", descriptor),
    ("variation", variation), ("sensitivity", sensitivity), ("escape_from", escape.fromObject),
    ("continuation", escape.continuation),
    ("source_record", if entry.sourceBound then some bridge else family),
    ("primitive", suppliedPrimitives), ("via_descriptor", input.viaDescriptor),
    ("output_evidence", input.outputEvidence), ("realization", some bridge),
    ("inline_actual", actual), ("inline_proof", some bridge),
    ("finite_bridge", some bridge)] : Array (String × Option Expr)).filterMap
      fun (slot, term) => term.map (slot, ·)
  let specializations ← liftM <| sourceSpecializations context slots specializedTerms
  let typeJson ← typeArgs.mapIdxM fun index value =>
    if typeArgSourceSlots[index]!.isSome then pure Json.null
    else expressionJson s!"type_args[{index}]" value
  let inlineBridgeInfo ← if sourceBacked slots "inline_proof" then
      some <$> getConstInfo entry.realizationName else pure none
  let bridgeSourceSlot := (#["inline_proof", "finite_bridge", "realization", "via_descriptor"] ++
    (if entry.sourceBound then #["source_record"] else #[]) ++
    (if generated then #["primitive"] else #[])).find? (sourceBacked slots)
  let mut usedLevels := collectLevelParams (collectLevelParams {} bridge) arena
  for expression in typeArgs ++ #[bridgeType, objectArena] ++
      #[suppliedPrimitives, descriptor, escape.fromObject, escape.continuation,
        variation, sensitivity, family].filterMap id do
    usedLevels := collectLevelParams usedLevels expression
  return Json.mkObj [
    ("owner", Json.str owner.toString), ("source_index", toJson index),
    ("source_text", Json.str input.sourceText), ("options", ← optionJson input.options),
    ("source_specializations", specializations),
    ("theorem", Json.str entry.theoremName.toString), ("level_params", namesJson levels),
    ("name_components", nameComponentsMap [
      ("owner", owner), ("theorem", entry.theoremName), ("unit", entry.unitName),
      ("arena", entry.arenaName), ("object_arena", entry.objectArenaName),
      ("realization", entry.realizationName),
      ("realization_source", input.realizationSource.getD .anonymous),
      ("variation", entry.variationWitness), ("sensitivity", entry.sensitivityWitness),
      ("catalog", entry.catalogId), ("resolved_arena", entry.resolvedArenaName),
      ("registration_module", entry.registrationModuleName)]),
    ("extra_level_params", namesJson (usedLevels.params.toList.filter (!levels.contains ·))),
    ("theorem_type", ← fallbackExpressionJson slots "theorem" "theorem_type" (some target.type)),
    ("theorem_type_source_slot", if sourceBacked slots "theorem" then Json.str "theorem" else Json.null),
    ("target_term", ← expressionJson "target_term"
      (mkConst entry.theoremName (levels.map Level.param))),
    ("type_args", Json.arr typeJson),
    ("type_arg_source_slots", Json.arr (typeArgSourceSlots.map fun slot =>
      slot.map Json.str |>.getD Json.null)),
    ("registration_universes", ← closedLevelsJson s!"registration: {owner}: {entry.theoremName}"
      (argumentLevels ++ implementationLevels)),
    ("bridge_kind", Json.str bridgeKind),
    ("bridge_type", ← if bridgeSourceSlot.isSome then pure Json.null
      else expressionJson "bridge_type" bridgeType),
    ("bridge_type_source_slot", bridgeSourceSlot.map Json.str |>.getD Json.null),
    ("generated", Json.bool generated),
    ("actual", ← if sourceBacked slots "inline_actual" || sourceBacked slots "actual" ||
        (generated && sourceBacked slots "primitive") then pure Json.null
      else optionalExpressionJson "actual" actual),
    ("bridge_arena", ← if bridgeArenaFromSource && sourceBacked slots "arena" then pure Json.null
      else expressionJson "bridge_arena" bridgeArena),
    ("bridge_arena_from_source", Json.bool bridgeArenaFromSource),
    ("arena_term", ← fallbackExpressionJson slots "arena" "arena_term" (some arena)),
    ("object_arena_term", ← if objectArena.consumeMData == arena.consumeMData && sourceBacked slots "arena" then
        pure Json.null else fallbackExpressionJson slots "object_arena" "object_arena_term" (some objectArena)),
    ("variation_term", ← fallbackExpressionJson slots "variation" "variation_term" variation),
    ("sensitivity_term", ← fallbackExpressionJson slots "sensitivity" "sensitivity_term" sensitivity),
    ("realization_term", ← if sourceBacked slots "inline_proof" || sourceBacked slots "finite_bridge" ||
        sourceBacked slots "via_descriptor" || (entry.sourceBound && sourceBacked slots "source_record") then pure Json.null else
      fallbackExpressionJson slots "realization" "realization_term" (some bridge)),
    ("inline_bridge_type", ← match inlineBridgeInfo with
      | none => pure Json.null
      | some info => expressionJson "inline_bridge_type" info.type),
    ("inline_bridge_level_params", inlineBridgeInfo.map (fun info => namesJson info.levelParams) |>.getD (Json.arr #[])),
    ("inline_bridge_term", ← if inlineBridgeInfo.isSome then expressionJson "inline_bridge_term" bridge else pure Json.null),
    ("unit", Json.str entry.unitName.toString), ("arena", Json.str entry.arenaName.toString),
    ("realization", Json.str entry.realizationName.toString),
    ("variation", Json.str (nameText entry.variationWitness)),
    ("sensitivity", Json.str (nameText entry.sensitivityWitness)),
    ("catalog", Json.str (nameText entry.catalogId)),
    ("object_arena", Json.str (nameText entry.objectArenaName)),
    ("resolved_arena", Json.str (nameText entry.resolvedArenaName)),
    ("registration_module", Json.str entry.registrationModuleName.toString),
    ("statement_identity", Json.str entry.statementIdentity),
    ("source_bound", Json.bool entry.sourceBound),
    ("source_target_matches", sourceTargetMatches.map Json.bool |>.getD Json.null),
    ("local_registration_names", Json.bool entry.localRegistrationNames),
    ("supplied_primitives", ← fallbackExpressionJson slots "primitive" "supplied_primitives" suppliedPrimitives),
    ("via_descriptor", ← fallbackExpressionJson slots "via_descriptor" "via_descriptor" input.viaDescriptor),
    ("output_evidence", ← fallbackExpressionJson slots "output_evidence" "output_evidence" input.outputEvidence),
    ("readout", ← fallbackExpressionJson slots "readout" "readout" descriptor),
    ("escape_from", ← fallbackExpressionJson slots "escape_from" "escape_from" escape.fromObject),
    ("continuation", ← fallbackExpressionJson slots "continuation" "continuation" escape.continuation),
    ("open_continuation", Json.bool escape.openContinuation),
    ("source_selection", escape.sourceSelection.map sourceSelectionJson |>.getD Json.null),
    ("realization_source", Json.str (input.realizationSource.map nameText |>.getD ""))]

private def enrollmentJson (owner : Name) (index : Nat) (input : TemplateEnrollmentInput)
    (context slots : Json) :
    MetaM Json := do
  let info ← getConstInfo input.name
  let mut constructors := #[]
  let mut constructorUniverse := Level.zero
  let mut usedLevels := collectLevelParams {} info.type
  let mut sourceTerms := #[("name", mkConst input.name (info.levelParams.map Level.param))]
  for index in [:input.constructors.size] do
    let name := input.constructors[index]!
    let type ← constantExpression name info.levelParams
    sourceTerms := sourceTerms.push (s!"constructor_{index}", type)
    usedLevels := collectLevelParams (collectLevelParams usedLevels type) (← inferType type)
    constructorUniverse := mkLevelMax constructorUniverse (← typeLevel type)
    constructors := constructors.push <| Json.mkObj [
      ("name", Json.str name.toString),
      ("name_components", Json.arr (nameComponents name)),
      ("type", ← fallbackExpressionJson slots s!"constructor_{index}" "constructor_type" (some type))]
  return Json.mkObj [
    ("owner", Json.str owner.toString), ("source_index", toJson index),
    ("name", Json.str input.name.toString), ("version", toJson input.version),
    ("name_components", nameComponentsMap [("owner", owner), ("name", input.name)]),
    ("constructors", Json.arr (input.constructors.map fun name => Json.str name.toString)),
    ("constructor_types", Json.arr constructors), ("level_params", namesJson info.levelParams),
    ("extra_level_params", namesJson (usedLevels.params.toList.filter (!info.levelParams.contains ·))),
    ("enrollment_universes", ← closedLevelsJson s!"template: {owner}: {input.name}"
      #[(← sortLevel info.type), constructorUniverse]),
    ("template_type", ← fallbackExpressionJson slots "name" "template_type" (some info.type)),
    ("template_type_source_slot", if sourceBacked slots "name" then Json.str "name" else Json.null),
    ("template_term", ← fallbackExpressionJson slots "name" "template_term"
      (some (mkConst input.name (info.levelParams.map Level.param)))),
    ("source_text", Json.str input.sourceText), ("options", ← optionJson input.options),
    ("source_specializations", ← sourceSpecializations context slots sourceTerms)]

private def sealJson (owner : Name) (index : Nat) (input : SealInput) : CoreM Json := do
  return Json.mkObj [
    ("owner", Json.str owner.toString), ("source_index", toJson index),
    ("root_id", Json.str input.rootId.toString),
    ("name_components", nameComponentsMap [("owner", owner), ("root_id", input.rootId)]),
    ("options", ← optionJson input.options)]

private def occurrenceJson (entry : SnapshotOccurrence) : MetaM Json := do
  let target ← getConstInfo entry.theoremName
  return Json.mkObj [
    ("object_arena", Json.str entry.objectArenaName.toString),
    ("theorem", Json.str entry.theoremName.toString),
    ("statement_identity", Json.str entry.statementIdentity),
    ("registration_module", Json.str entry.registrationModuleName.toString),
    ("name_components", nameComponentsMap [
      ("object_arena", entry.objectArenaName), ("theorem", entry.theoremName),
      ("registration_module", entry.registrationModuleName)]),
    ("captured_statement", ← optionalExpressionJson "captured_statement" entry.capturedStatement),
    ("target_term", ← expressionJson "target_term"
      (mkConst entry.theoremName (target.levelParams.map Level.param))),
    ("level_params", namesJson target.levelParams)]

private def rootJson (owner : Name) (index : Nat) (entry : RootCatalogContract) : MetaM Json := do
  return Json.mkObj [
    ("owner", Json.str owner.toString), ("source_index", toJson index),
    ("root_id", Json.str entry.rootId.toString),
    ("name_components", nameComponentsMap [
      ("owner", owner), ("root_id", entry.rootId),
      ("companion_prefix", entry.companionPrefix.getD .anonymous)]),
    ("expected", Json.arr (← entry.expected.mapM fun occurrence =>
      withMetaInputContext s!"root.expected: {owner}: {entry.rootId}: {occurrence.theoremName}"
        (occurrenceJson occurrence))),
    ("source", Json.arr (← entry.source.mapM fun occurrence =>
      withMetaInputContext s!"root.source: {owner}: {entry.rootId}: {occurrence.theoremName}"
        (occurrenceJson occurrence))),
    ("baseline", Json.arr (← entry.baseline.mapM fun occurrence =>
      withMetaInputContext s!"root.baseline: {owner}: {entry.rootId}: {occurrence.theoremName}"
        (occurrenceJson occurrence))),
    ("companion_prefix", Json.str (entry.companionPrefix.map Name.toString |>.getD ""))]

private def indexedOwned (inputs : Array (Name × α)) : Array (Name × Nat × α) := Id.run do
  let mut indices : NameMap Nat := {}
  let mut result := #[]
  for (owner, input) in inputs do
    let index := (indices.find? owner).getD 0
    result := result.push (owner, index, input)
    indices := indices.insert owner (index + 1)
  return result

private def compiledSource (repo : System.FilePath) (owner : Name) : IO Json := do
  let relative := String.intercalate "/" (owner.toString.splitOn ".") ++ ".lean"
  let source ← IO.FS.readFile (repo / relative)
  let olean ← findOLean owner
  let tracePath := olean.withExtension "trace"
  let trace ← match Json.parse (← IO.FS.readFile tracePath) with
    | .ok trace => pure trace
    | .error _ => throw <| IO.userError s!"RM-INPUT-TRACE-JSON: {owner}"
  unless (trace.getObjValAs? Bool "synthetic").toOption == some false do
    throw <| IO.userError s!"RM-INPUT-TRACE-SYNTHETIC: {owner}"
  let inputs ← match trace.getObjValAs? (Array Json) "inputs" with
    | .ok inputs => pure inputs
    | .error _ => throw <| IO.userError s!"RM-INPUT-TRACE-INPUTS: {owner}"
  let mut sourceHashes : Array String := #[]
  for input in inputs do
    if let .ok row := input.getArr? then
      if let some key := row[0]? then
        if let .ok key := key.getStr? then
          if key.endsWith ("/" ++ relative) || key == relative then
            if let some value := row[1]? then
              if let .ok value := value.getStr? then sourceHashes := sourceHashes.push value
  unless sourceHashes.size == 1 && sourceHashes[0]! == toString (Lake.Hash.ofText source) do
    throw <| IO.userError s!"RM-INPUT-SNAPSHOT-SOURCE: {owner}"
  let artifactHash ← IO.FS.readFile (olean.toString ++ ".hash")
  let expectedHash ← match trace.getObjVal? "outputs" >>= (·.getObjValAs? (Array String) "o") with
    | .ok hashes => pure hashes
    | .error _ => throw <| IO.userError s!"RM-INPUT-TRACE-OUTPUTS: {owner}"
  unless expectedHash.contains (artifactHash.trimAscii.toString ++ ".olean") do
    throw <| IO.userError s!"RM-INPUT-SNAPSHOT-ARTIFACT: {owner}"
  return Json.mkObj [("path", Json.str relative), ("owner", Json.str owner.toString),
    ("source_text", Json.str source), ("trace_verified", Json.bool true),
    ("trace_source_hash", Json.str sourceHashes[0]!)]

private def sourceCommand (snapshot : Json) (owner : Name) (index : Nat) (category : String) :
    MetaM Json := do
  let files ← Lean.ofExcept <| snapshot.getObjValAs? (Array Json) "files"
  let path := String.intercalate "/" (owner.toString.splitOn ".") ++ ".lean"
  let some file := files.find? (fun file => (file.getObjValAs? String "path").toOption == some path)
    | throwError "RM-INPUT-SYNTAX-OWNER: {owner}"
  let commands ← Lean.ofExcept <| file.getObjValAs? (Array Json) "commands"
  let commands := commands.filter fun command =>
    (command.getObjValAs? String "kind").toOption == some category
  let some command := commands[index]? | throwError "RM-INPUT-SYNTAX-INDEX: {owner}: {category}: {index}"
  return command

private partial def companionPrefix (name : Name) : Option Name :=
  match name with
  | .anonymous => none
  | .num parent _ => companionPrefix parent
  | .str parent word =>
    if word == "__information_unit" || word == "__primitive_realization" then some name
    else companionPrefix parent

private def decodeNameComponents (object : Json) (key : String) : MetaM Name := do
  let components ← Lean.ofExcept <| object.getObjValAs? (Array Json) key
  components.foldlM (init := Name.anonymous) fun parent component =>
    match component.getStr? with
    | .ok word => pure (.str parent word)
    | .error _ => do
      let value ← Lean.ofExcept <| fromJson? (α := Nat) component
      return .num parent value

private def decodeOpens (command : Json) : MetaM (List OpenDecl) := do
  let declarations ← Lean.ofExcept <| command.getObjValAs? (Array Json) "open_decls"
  declarations.toList.mapM fun (declaration : Json) => do
    let kind ← Lean.ofExcept <| declaration.getObjValAs? String "kind"
    if kind == "simple" then
      let ns ← decodeNameComponents declaration "namespace_components"
      let exceptions ← Lean.ofExcept <| declaration.getObjValAs? (Array String) "exceptions"
      return .simple ns (exceptions.toList.map String.toName)
    else if kind == "explicit" then
      let name ← decodeNameComponents declaration "name_components"
      let target ← decodeNameComponents declaration "declaration_components"
      return .explicit name target
    else throwError "RM-INPUT-OPEN-DECL"

private partial def companionClosure (name anchor : Name) (seen : NameSet) :
    MetaM (NameSet × Array Json) := do
  if seen.contains name then return (seen, #[])
  let env ← getEnv
  let info ← getConstInfo name
  let some body := info.value? (allowOpaque := true)
    | throwError "RM-INPUT-COMPANION-BODY: {name}"
  let mut seen := seen.insert name
  let mut result := #[]
  let dependencies := info.getUsedConstantsAsSet.toArray.filter
    (fun dependency => companionPrefix dependency == some dependency)
  let dependencies := dependencies.qsort (fun left right => left.toString < right.toString)
  for dependency in dependencies do
    let closure ← companionClosure dependency anchor seen
    seen := closure.1
    result := result ++ closure.2
  let some index := env.getModuleIdxFor? name | throwError "RM-INPUT-COMPANION-OWNER: {name}"
  let owner := env.header.moduleNames[index.toNat]!
  let anchor := ((RegistrationInputs.owned env).find? fun (_, input) =>
    input.entry.unitName == name || input.entry.realizationName == name).map
      (fun (_, input) => input.entry.unitName) |>.getD anchor
  let (printedType, printedBody) ← withMetaInputContext s!"companion: {owner}: {name}" <|
    withEnv (env.setMainModule owner) do
      let printedType ← expressionJson s!"companion_type: {owner}: {name}" info.type
      let printedBody ← expressionJson s!"companion_body: {owner}: {name}" body
      pure (printedType, printedBody)
  result := result.push <| Json.mkObj [
    ("name", Json.str name.toString), ("anchor_unit", Json.str anchor.toString),
    ("name_components", nameComponentsMap [
      ("name", name), ("anchor_unit", anchor), ("owner", owner)]),
    ("owner", Json.str owner.toString), ("private", Json.bool false),
    ("companion_dependencies", Json.arr (dependencies.map fun name => Json.str name.toString)),
    ("level_params", namesJson info.levelParams),
    ("type", printedType), ("body", printedBody)]
  return (seen, result)

private def companionInputs (snapshot : Json) : MetaM (Json × Json) := do
  let env ← getEnv
  let files ← Lean.ofExcept <| snapshot.getObjValAs? (Array Json) "files"
  let rawNames := (RegistrationInputs.owned env).map fun (owner, input) => (owner, input.entry.unitName)
  let mut bindings := #[]
  let mut companions := #[]
  let mut seen : NameSet := {}
  for file in files do
    let path ← Lean.ofExcept <| file.getObjValAs? String "path"
    let owner := (String.intercalate "." (path.splitOn "/")).dropEnd 5 |>.toString |>.toName
    let commands ← Lean.ofExcept <| file.getObjValAs? (Array Json) "commands"
    for command in commands do
      let identifiers ← Lean.ofExcept <| command.getObjValAs? (Array Json) "companion_identifiers"
      if identifiers.isEmpty then continue
      let ns ← decodeNameComponents command "namespace_components"
      let opens ← decodeOpens command
      for identifier in identifiers do
        let sourceName ← Lean.ofExcept <| identifier.getObjValAs? String "name"
        let sourceId ← decodeNameComponents identifier "name_components"
        let candidates := ResolveName.resolveGlobalName (env.setMainModule owner) {} ns opens sourceId
        let names := candidates.filterMap fun (name, suffix) => if suffix.isEmpty then some name else none
        let names := if names.isEmpty then
          (rawNames.filterMap fun (module, name) =>
            if module == owner && privateToUserName name == sourceId then some name else none).toList
          else names
        let [name] := names | throwError "RM-INPUT-COMPANION-RESOLUTION: {path}: {sourceName}"
        bindings := bindings.push <| Json.mkObj [
          ("path", Json.str path), ("name", Json.str name.toString),
          ("start", ← Lean.ofExcept <| identifier.getObjVal? "start"),
          ("end", ← Lean.ofExcept <| identifier.getObjVal? "end")]
        let closure ← companionClosure name name seen
        seen := closure.1
        companions := companions ++ closure.2
  return (Json.arr companions, Json.arr bindings)

private def withInputContext (label : String) (action : TermElabM Json) : TermElabM Json :=
  withCurrHeartbeats <| tryCatchRuntimeEx action fun error => withCurrHeartbeats do
    let message ← addMessageContextFull error.toMessageData
    throw <| Exception.error Syntax.missing m!"RM-INPUT-ROW: {label}: {message}"

private def extract (env : Environment) (repo : System.FilePath) (syntaxSnapshot : Json) : TermElabM Json := do
  let mut owners : Array Name := env.header.moduleNames.filter ((`Reg).isPrefixOf ·)
  for owner in (RegistrationInputs.owned env).map (·.1) ++
      (TemplateEnrollmentInputs.owned env).map (·.1) ++
      (SealInputs.owned env).map (·.1) ++ (RootCatalogs.owned env).map (·.1) do
    if (`Reg).isPrefixOf owner && !owners.contains owner then owners := owners.push owner
  owners := owners.qsort (fun left right => left.toString < right.toString)
  let compiledSources ← liftM <| owners.mapM (compiledSource repo)
  let syntaxFiles ← Lean.ofExcept <| syntaxSnapshot.getObjValAs? (Array Json) "files"
  for compiled in compiledSources do
    let path ← Lean.ofExcept <| compiled.getObjValAs? String "path"
    let source ← Lean.ofExcept <| compiled.getObjValAs? String "source_text"
    let some parsed := syntaxFiles.find? (fun file =>
      (file.getObjValAs? String "path").toOption == some path)
      | throwError "RM-INPUT-SYNTAX-OWNER: {path}"
    unless (parsed.getObjValAs? String "source_text").toOption == some source do
      throwError "RM-INPUT-SYNTAX-SOURCE: {path}"
  let (companions, companionBindings) ← companionInputs syntaxSnapshot
  return Json.mkObj [
    ("schema", Json.str "reg-migration-inputs-v2"),
    ("compiled_sources", Json.arr compiledSources),
    ("companions", companions), ("companion_bindings", companionBindings),
    ("registrations", Json.arr (← (indexedOwned (RegistrationInputs.owned env)).mapM
      fun (owner, index, input) => do
        withEnv (env.setMainModule owner) <| withInputContext s!"registration: {owner}: {input.entry.theoremName}" do
          let context ← sourceCommand syntaxSnapshot owner index "registration"
          registrationJson owner index input context (← Lean.ofExcept <| context.getObjVal? "slots"))),
    ("templates", Json.arr (← (indexedOwned (TemplateEnrollmentInputs.owned env)).mapM
      fun (owner, index, input) => do
        withEnv (env.setMainModule owner) <| withInputContext s!"template: {owner}: {input.name}" do
          let context ← sourceCommand syntaxSnapshot owner index "template"
          let slots ← Lean.ofExcept <| context.getObjVal? "slots"
          liftM <| enrollmentJson owner index input context slots)),
    ("seals", Json.arr (← (indexedOwned (SealInputs.owned env)).mapM
      fun (owner, index, input) => sealJson owner index input)),
    ("roots", Json.arr (← (indexedOwned (RootCatalogs.owned env)).mapM
      fun (owner, index, input) =>
        withEnv (env.setMainModule owner) <| withInputContext s!"root: {owner}: {input.rootId}"
          (liftM <| rootJson owner index input)))]

syntax (name := regMigrationExtract) "#reg_migration_extract " str str : command

elab_rules : command
  | `( #reg_migration_extract $snapshot:str $path:str ) => do
    let snapshot ← liftIO <| IO.FS.readFile snapshot.getString
    let snapshot ← Lean.ofExcept <| Json.parse snapshot
    let output ← liftTermElabM <| extract (← getEnv) "." snapshot
    liftIO <| IO.FS.writeFile path.getString (output.compress ++ "\n")

private def ioJson (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw <| IO.userError s!"{label}: {error}"

/-- Native extraction imports the snapshot before creating its Meta and Term contexts. -/
def extractorMain (args : List String) : IO UInt32 := do
  try
    let ["--manifest", manifest, output] := args
      | do
        IO.eprintln "RM-INPUT-USAGE: --manifest MANIFEST OUTPUT"
        return 2
    initSearchPath (← findSysroot)
    let manifest ← ioJson "RM-INPUT-MANIFEST-JSON" <| Json.parse (← IO.FS.readFile manifest)
    let modules ← ioJson "RM-INPUT-MANIFEST-MODULES" <|
      manifest.getObjValAs? (Array String) "modules"
    let repo := (manifest.getObjValAs? String "repo").toOption.getD "."
    let snapshotPath ← ioJson "RM-INPUT-MANIFEST-SYNTAX" <|
      manifest.getObjValAs? String "syntax_snapshot"
    let snapshot ← ioJson "RM-INPUT-SYNTAX-JSON" <|
      Json.parse (← IO.FS.readFile snapshotPath)
    unsafe enableInitializersExecution
    let imports := modules.map fun name => ({ module := name.toName } : Import)
    let env ← importModules imports {} (loadExts := true)
    let action : MetaM Json := (extract env repo snapshot).run'
    let action : MetaM Json := tryCatchRuntimeEx action fun error => do
      let message ← addMessageContextFull error.toMessageData
      throw <| Exception.error Syntax.missing m!"RM-INPUT-EXTRACT: {message}"
    let (result, _) ← action.run' |>.toIO
      { fileName := "<reg-migration-extract>", fileMap := default } { env }
    IO.FS.writeFile output (result.compress ++ "\n")
    return 0
  catch error =>
    IO.eprintln s!"RM-INPUT-FAIL: {error}"
    return 1

end LeanInformationAudit.RegMigration

def main (args : List String) : IO UInt32 :=
  LeanInformationAudit.RegMigration.extractorMain args
