import LeanInformationAuditRegAnalysis.K2FactsGeneratorCore
import LeanInformationAuditRegTests.Fixtures.Provenance

namespace K2HeadFamiliesGenerator
open Lean Meta K2FactsGenerator

def decodeName (input : Json) : Except String Name := do
  let mut result := Name.anonymous
  for component in ← input.getArr? do
    match component with
    | .str text => result := .str result text
    | .num _ => result := .num result (← component.getNat?)
    | _ => throw "family.name_component"
  return result

partial def decodeLevel (input : Json) : Except String Level := do
  let fields ← input.getArr?
  match ← fields[0]!.getStr? with
  | "zero" => return .zero
  | "param" => return .param (← decodeName fields[1]!)
  | "succ" => return .succ (← decodeLevel fields[1]!)
  | "max" => return .max (← decodeLevel fields[1]!) (← decodeLevel fields[2]!)
  | "imax" => return .imax (← decodeLevel fields[1]!) (← decodeLevel fields[2]!)
  | _ => throw "family.level_constructor"

private def lambdaClose (xs : Array Expr) (value : Expr) : MetaM Expr :=
  mkLambdaFVars xs value (usedOnly := false) (usedLetOnly := false)
    (etaReduce := false) (generalizeNondepLet := false)

private def typeClose (xs : Array Expr) (type : Expr) : MetaM Expr :=
  mkForallFVars xs type (usedOnly := false) (usedLetOnly := false)
    (generalizeNondepLet := false)

private def parameters (xs : Array Expr) : MetaM (Array Expr) := do
  let lctx ← getLCtx
  xs.filterM fun x => return ((lctx.get! x.fvarId!).value? (allowNondep := true)).isNone

private def closingPath (xs : Array Expr) : MetaM (List String) := do
  let lctx ← getLCtx
  xs.toList.mapM fun x => do
    return if ((lctx.get! x.fvarId!).value? (allowNondep := true)).isSome then
      "letBody" else "body"

private partial def endsInSort : Expr → Bool
  | .forallE _ _ body _ | .letE _ _ _ body _ => endsInSort body
  | .sort _ => true
  | _ => false

private def usedLevels (levels : List Name) (value type : Expr) : List Name :=
  let used := (collectLevelParams (collectLevelParams {} value) type).params
  levels.filter used.contains

private structure ConstructorDAG where
  nodes : Array Json := #[]
  indices : ExprStructMap Nat := {}

private abbrev ConstructorM := StateT ConstructorDAG (Except String)

private def binderTag : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

private partial def constructorNode (expression : Expr) : ConstructorM Nat := do
  if let some index := (← get).indices[ExprStructEq.mk expression]? then return index
  let node ← match expression with
    | .bvar index => pure <| toJson #[Json.str "bvar", toJson index]
    | .sort universeLevel => pure <| toJson #[Json.str "sort", levelTree universeLevel]
    | .const name levels => pure <| toJson #[Json.str "const", toJson (nameComponents name),
        toJson (levels.map levelTree)]
    | .app function argument => do
        let function ← constructorNode function
        let argument ← constructorNode argument
        pure <| toJson #[Json.str "app", toJson function, toJson argument]
    | .lam name domain body mode => do
        let domain ← constructorNode domain
        let body ← constructorNode body
        pure <| toJson #[Json.str "lam", toJson (nameComponents name), toJson (binderTag mode),
          toJson domain, toJson body]
    | .forallE name domain body mode => do
        let domain ← constructorNode domain
        let body ← constructorNode body
        pure <| toJson #[Json.str "forall", toJson (nameComponents name), toJson (binderTag mode),
          toJson domain, toJson body]
    | .letE name type value body nondependent => do
        let type ← constructorNode type
        let value ← constructorNode value
        let body ← constructorNode body
        pure <| toJson #[Json.str "let", toJson (nameComponents name), toJson type,
          toJson value, toJson body, toJson nondependent]
    | .lit (.natVal value) => pure <| toJson #[Json.str "nat", toJson value]
    | .lit (.strVal value) => pure <| toJson #[Json.str "str", toJson value]
    | .proj name index body => do
        let body ← constructorNode body
        pure <| toJson #[Json.str "proj", toJson (nameComponents name), toJson index, toJson body]
    | .mdata _ body => do
        let body ← constructorNode body
        pure <| toJson #[Json.str "mdata", toJson body]
    | .fvar _ | .mvar _ => throw "family.term_not_closed"
  let index := (← get).nodes.size
  modify fun state => { state with
    nodes := state.nodes.push node
    indices := state.indices.insert (ExprStructEq.mk expression) index }
  return index

/-- Constructor transport builds a new helper with empty metadata annotations.
 Native source/candidate keys retain their original Exprs; the generated Reg
 definitions and Exact facts must compile independently. The DAG map is local
 to one literal and stores structural node indices, never assessed outcomes. -/
private def constructorTerm (expression : Expr) : MetaM String := do
  diagnosticStage.modify fun (_, name, part, path) => ("postprocess-constructor-term", name, part, path)
  unless !expression.hasFVar && !expression.hasMVar && !expression.hasLooseBVars do
    throwError "family.term_not_closed"
  let (_, dag) ← IO.ofExcept <| (constructorNode expression).run {}
  return "(compiled_term% " ++ (Json.str (Json.arr dag.nodes).compress).compress ++ ")"

private def helper (name : Name) (levels : List Name) (type value : Expr) : MetaM Json := do
  let valueText ← constructorTerm value
  return Json.mkObj [
    ("name", toJson name), ("declarationComponents", toJson (nameComponents name)),
    ("nameTemplate", toJson ("${HEAD}." ++ name.getString!)),
    ("levels", toJson levels), ("usedLevels", toJson (usedLevels levels value type)),
    ("coordinateLevels", toJson (levels.map (fun level => levelText (.param level)))),
    ("coordinateLevelTrees", toJson (levels.map (fun level => levelTree (.param level)))),
    ("type", toJson ("type_of% (" ++ valueText ++ ")")), ("value", toJson valueText),
    ("explicitTypeRequired", toJson true)]

private def location (name : Name) (path : List String) (levels : List Name) : Json :=
  Json.mkObj [
    ("declarationComponents", toJson (nameComponents name)),
    ("part", toJson "value"), ("path", toJson path),
    ("coordinateLevelTrees", toJson (levels.map (fun level => levelTree (.param level))))]

private def addHelper (name : Name) (levels : List Name) (type value : Expr) : MetaM Unit := do
  addDecl <| .defnDecl {
    name, levelParams := levels, type, value
    hints := .abbrev
    safety := .safe }

private partial def etaClose (xs : Array Expr) (value application : Expr) :
    MetaM (Expr × List String) := do
  match value with
  | .lam name domain body mode =>
    withLocalDecl name mode domain fun x =>
      etaClose (xs.push x) (body.instantiate1 x) (mkApp application x)
  | .letE name domain assigned body nd =>
    withLetDecl name domain assigned (nondep := nd) fun x =>
      etaClose (xs.push x) (body.instantiate1 x) application
  | _ => return (← lambdaClose xs application, ← closingPath xs)

private structure FamilyState where
  families : Array Json := #[]
  helpers : Array (Name × List Name × Expr × Expr) := #[]
  checks : Array (Expr × Expr × Expr) := #[]
  next : Nat := 0

private abbrev FamilyM := StateRefT FamilyState MetaM

private partial def lift (stem : Name) (levels : List Name) (xs : Array Expr)
    (path : List String) (expression : Expr) (proper : Bool) (depth : Nat := 0) : FamilyM Expr := do
  if depth > 256 then throwError "family.depth:{stem}"
  if proper && expression.isLambda && endsInSort (← inferType expression) then
    let index := (← get).next
    modify fun state => { state with next := index + 1 }
    let fName := .str stem s!"__fieldF_{index}"
    let etaName := .str stem s!"__fieldEta_{index}"
    let fValue ← lambdaClose xs expression
    let fType ← typeClose xs (← inferType expression)
    let helperLevels := usedLevels levels fValue fType
    addHelper fName helperLevels fType fValue
    modify fun state => { state with
      helpers := state.helpers.push (fName, helperLevels, fType, fValue) }
    let f := mkConst fName (helperLevels.map Level.param)
    let applied := mkAppN f (← parameters xs)
    let (etaValue, etaBodyPath) ← etaClose xs expression applied
    let etaType ← inferType etaValue
    addHelper etaName helperLevels etaType etaValue
    modify fun state => { state with
      helpers := state.helpers.push (etaName, helperLevels, etaType, etaValue) }
    let argumentValue ← lambdaClose xs applied
    unless ← isDefEq argumentValue etaValue do throwError "family.eta:{fName}"
    unless ← isDefEq etaValue fValue do throwError "family.body:{fName}"
    modify fun state => { state with
      checks := state.checks.push (argumentValue, etaValue, fValue) }
    let family := Json.mkObj [
      ("index", toJson index), ("headArgumentPath", toJson path),
      ("headArgumentClosed", toJson (← constructorTerm argumentValue)),
      ("function", ← helper fName helperLevels fType fValue),
      ("eta", ← helper etaName helperLevels etaType etaValue),
      ("etaBodyPath", toJson etaBodyPath),
      ("relations", toJson #[
        Json.mkObj [("kind", toJson "exact"), ("left", location stem path levels),
          ("right", location etaName [] helperLevels),
          ("nameTemplate", toJson ("${HEAD}.__fieldExact_" ++ toString index ++ "_eta"))],
        Json.mkObj [("kind", toJson "exact"),
          ("left", location etaName etaBodyPath helperLevels),
          ("right", location fName [] helperLevels),
          ("nameTemplate", toJson ("${HEAD}.__fieldExact_" ++ toString index ++ "_body"))]])]
    modify fun state => { state with families := state.families.push family }
    return applied
  let child := fun edge expression => lift stem levels xs (path ++ [edge]) expression true (depth + 1)
  match expression with
  | .app function argument => return .app (← child "function" function) (← child "argument" argument)
  | .lam name domain body mode =>
    withLocalDecl name mode domain fun x => do
      let actualBody ← lift stem levels (xs.push x) (path ++ ["body"])
        (body.instantiate1 x) false (depth + 1)
      return ← lambdaClose #[x] actualBody
  | .forallE name domain body mode =>
    withLocalDecl name mode domain fun x => do
      let actualBody ← lift stem levels (xs.push x) (path ++ ["body"])
        (body.instantiate1 x) true (depth + 1)
      return ← typeClose #[x] actualBody
  | .letE name domain assigned body nd =>
    withLetDecl name domain assigned (nondep := nd) fun x => do
      let actualBody ← lift stem levels (xs.push x) (path ++ ["letBody"])
        (body.instantiate1 x) true (depth + 1)
      return ← lambdaClose #[x] actualBody
  | .mdata data body => return .mdata data (← child "metadata" body)
  | .proj name index body => return .proj name index (← child "projection" body)
  | _ => return expression

partial def atSource (node : Expr) (path : List String) (xs : Array Expr)
    (action : Array Expr → Expr → MetaM α) : MetaM α := do
  match path with
  | [] => action xs node
  | edge :: rest =>
    match edge, node with
    | "function", .app function _ => atSource function rest xs action
    | "argument", .app _ argument => atSource argument rest xs action
    | "domain", .lam _ domain _ _ | "domain", .forallE _ domain _ _ =>
      atSource domain rest xs action
    | "body", .lam name domain body mode | "body", .forallE name domain body mode =>
      withLocalDecl name mode domain fun x => atSource (body.instantiate1 x) rest (xs.push x) action
    | "letType", .letE _ domain _ _ _ => atSource domain rest xs action
    | "letValue", .letE _ _ assigned _ _ => atSource assigned rest xs action
    | "letBody", .letE name domain assigned body nd =>
      withLetDecl name domain assigned (nondep := nd) fun x =>
        atSource (body.instantiate1 x) rest (xs.push x) action
    | "metadata", .mdata _ body | "projection", .proj _ _ body => atSource body rest xs action
    | _, _ => throwError "family.coordinate_shape:{edge}"

private structure OpenedSource where
  node : Expr
  xs : Array Expr
  lctx : LocalContext
  localInstances : LocalInstances
  contextID : Nat
  telescopeNoMVars : Bool
  eligible : Bool
  deriving Inhabited

private abbrev SourceRootKey := Name × String × ExprStructEq
private abbrev SourcePathKey := SourceRootKey × List String

initialize sourcePaths : IO.Ref (PHashMap SourcePathKey OpenedSource) ← IO.mkRef {}
initialize sourcePathReuse : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)
initialize sourceContextIDs : IO.Ref Nat ← IO.mkRef 1

private def freshSourceContext : IO Nat := do
  let contextID ← sourceContextIDs.get
  sourceContextIDs.set (contextID + 1)
  return contextID

private def captureSource (contextID : Nat) (telescopeNoMVars : Bool)
    (xs : Array Expr) (node : Expr) : MetaM OpenedSource := do
  return {
    node, xs, lctx := ← getLCtx, localInstances := ← getLocalInstances,
    contextID, telescopeNoMVars, eligible := telescopeNoMVars && !node.hasMVar }

private def captureRootSource (node : Expr) : MetaM OpenedSource := do
  let lctx ← getLCtx
  let localInstances ← getLocalInstances
  let contextID ← if lctx.isEmpty && localInstances.isEmpty then pure 0
    else freshSourceContext
  captureSource contextID true #[] node

private def captureChildSource (parent : OpenedSource) (bound : Bool)
    (xs : Array Expr) (node : Expr) : MetaM OpenedSource := do
  let contextID ← if bound then freshSourceContext else pure parent.contextID
  let mut telescopeNoMVars := parent.telescopeNoMVars
  if bound then
    let declaration := (← getLCtx).getFVar! xs[xs.size - 1]!
    telescopeNoMVars := telescopeNoMVars && !declaration.type.hasMVar &&
      (match declaration.value? (allowNondep := true) with
       | some value => !value.hasMVar
       | none => true)
  captureSource contextID telescopeNoMVars xs node

/-- A path prefix retains its actual local context, local instances, telescope,
 and unmodified compiler expression. Reopening that context does not infer or
 normalize a node. The module reset prevents reuse across source environments. -/
private partial def openedSource (key : SourceRootKey) (path : List String) :
    MetaM OpenedSource := do
  if let some opened := (← sourcePaths.get).find? (key, path) then
    sourcePathReuse.modify fun (hits, misses) => (hits + 1, misses)
    return opened
  sourcePathReuse.modify fun (hits, misses) => (hits, misses + 1)
  let edge :: reversedPrefix := path.reverse |
    throwError "family.source_root_not_installed"
  let parent ← openedSource key reversedPrefix.reverse
  let bound := match edge, parent.node with
    | "body", .lam .. | "body", .forallE .. | "letBody", .letE .. => true
    | _, _ => false
  let opened ← withLCtx parent.lctx parent.localInstances <|
    atSource parent.node [edge] parent.xs (captureChildSource parent bound)
  sourcePaths.modify (·.insert (key, path) opened)
  return opened

private def withSource (
    row : Json) (action : ConstantInfo → List Level → OpenedSource → MetaM α) :
    MetaM α := do
  let name ← IO.ofExcept <| decodeName (← IO.ofExcept <| row.getObjVal? "declarationComponents")
  let some info := (← getEnv).find? name | throwError "family.source_missing:{name}"
  let part ← IO.ofExcept <| (← IO.ofExcept <| row.getObjVal? "part").getStr?
  let path ← IO.ofExcept <| (← IO.ofExcept <| row.getObjVal? "path").getArr? >>= fun values =>
    values.toList.mapM Json.getStr?
  let levels ← IO.ofExcept <| (← IO.ofExcept <| row.getObjVal? "coordinateLevelTrees").getArr? >>= fun values =>
    values.toList.mapM decodeLevel
  let source ← if part == "type" then pure info.type else
    match info with
    | .defnInfo definition => pure definition.value
    | _ => throwError "family.source_value:{name}"
  let key : SourceRootKey := (name, part, ExprStructEq.mk (mkConst `K2RawCoordinateLevels levels))
  if ((← sourcePaths.get).find? (key, ([] : List String))).isNone then
    let source := if levels == info.levelParams.map Level.param then source else
      LeanInformationAudit.Contract.Literal.instantiateRawLevels info.levelParams levels source
    let opened ← captureRootSource source
    sourcePaths.modify (·.insert (key, ([] : List String)) opened)
  let opened ← openedSource key path
  withLCtx opened.lctx opened.localInstances (action info levels opened)

private def reusableClosed (expression : Expr) : Bool :=
  !expression.hasFVar && !expression.hasMVar && !expression.hasLooseBVars

private structure SourceType where
  closedType : Expr
  references : List Name
  deriving Inhabited

private structure ClosedSource where
  closedOriginal : Expr
  sourceType : SourceType
  rawKey : String
  deriving Inhabited

private abbrev ClosedSourceKey :=
  ExprStructEq × Nat × ExprStructEq × List Name × Name

initialize closedSources : IO.Ref (PHashMap ClosedSourceKey ClosedSource) ← IO.mkRef {}
initialize closedSourceReuse : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)

private abbrev SourceTypeKey := ExprStructEq × Nat × List Name × Name

initialize sourceTypes : IO.Ref
    (PersistentExprStructMap (PHashMap SourceTypeKey SourceType)) ← IO.mkRef {}
initialize sourceTypeReuse : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)

private structure CompletedHead where
  stem : Name
  closedHead : Expr
  liftedHead : Expr
  liftedHeadText : String
  normalizedReferences : List Name
  state : FamilyState

private abbrev CompletedHeadKey := ExprStructEq × ExprStructEq × Nat × List Name × Name

initialize completedHeads : IO.Ref
    (PersistentExprStructMap (PHashMap CompletedHeadKey CompletedHead)) ← IO.mkRef {}
initialize completedHeadReuse : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)

def resetCompletedHeads : IO Unit := do
  closedSources.set {}
  closedSourceReuse.set (0, 0)
  sourceContextIDs.set 1
  sourcePaths.set {}
  sourcePathReuse.set (0, 0)
  sourceTypes.set {}
  sourceTypeReuse.set (0, 0)
  completedHeads.set {}
  completedHeadReuse.set (0, 0)

private def phase (stage : String) : IO Unit :=
  diagnosticStage.modify fun (_, declaration, part, path) => (stage, declaration, part, path)

/-- The complete closure includes every enclosing binder domain and let value.
 Only closed, metavariable-free results are reusable in the current module. -/
private def checkedSourceType (scope : Name) (scopeLevels : List Name)
    (levels : List Level) (xs : Array Expr) (original closedOriginal : Expr) :
    MetaM SourceType := do
  let levelOperand := mkConst `K2RawCoordinateLevels levels
  let eligible := reusableClosed closedOriginal && reusableClosed levelOperand
  let key : SourceTypeKey := (ExprStructEq.mk levelOperand, xs.size, scopeLevels, scope)
  phase "postprocess-source-type-lookup"
  if eligible then
    if let some result := ((← sourceTypes.get).find? (ExprStructEq.mk closedOriginal)).bind (fun entries => entries.find? key) then
      sourceTypeReuse.modify fun (hits, misses) => (hits + 1, misses)
      return result
  sourceTypeReuse.modify fun (hits, misses) => (hits, misses + 1)
  phase "postprocess-infer-type"
  let originalType ← K2FactsGenerator.inferNodeType original
  phase "postprocess-close-type"
  let closedType ← typeClose xs originalType
  let result : SourceType := { closedType, references := originalType.getUsedConstants.toList }
  if eligible && reusableClosed closedType then
    sourceTypes.modify fun cache =>
      let entries := (cache.find? (ExprStructEq.mk closedOriginal)).getD {}
      cache.insert (ExprStructEq.mk closedOriginal) (entries.insert key result)
  return result

/-- Reuse the original closure, checked type and raw key only for one exact
 open node, actual lexical context, raw levels and current module/scope. -/
private def prepareClosedSource (scope : Name) (scopeLevels : List Name)
    (levels : List Level) (opened : OpenedSource) :
    MetaM (ClosedSourceKey × Bool × Expr × SourceType × Option String) := do
  let levelOperand := mkConst `K2RawCoordinateLevels levels
  let key : ClosedSourceKey := (ExprStructEq.mk opened.node, opened.contextID,
    ExprStructEq.mk levelOperand, scopeLevels, scope)
  let eligible := opened.eligible && reusableClosed levelOperand
  phase "postprocess-closed-source-lookup"
  if eligible then
    if let some result := (← closedSources.get).find? key then
      closedSourceReuse.modify fun (hits, misses) => (hits + 1, misses)
      return (key, eligible, result.closedOriginal, result.sourceType, some result.rawKey)
  closedSourceReuse.modify fun (hits, misses) => (hits, misses + 1)
  phase "postprocess-close"
  let closedOriginal ← lambdaClose opened.xs opened.node
  let sourceType ← checkedSourceType scope scopeLevels levels opened.xs opened.node closedOriginal
  return (key, eligible, closedOriginal, sourceType, none)

/-- Publish only at the original raw-key call site, after preceding head checks,
 so a failed row retains the original raw-key insertion order. -/
private def completeClosedSource (key : ClosedSourceKey) (eligible : Bool)
    (closedOriginal : Expr) (sourceType : SourceType) (levels : List Level)
    (cachedRawKey : Option String) : IO String := do
  if let some rawKey := cachedRawKey then return rawKey
  let rawKey ← K2FactsGenerator.rawBindingKey closedOriginal sourceType.closedType levels
  if eligible && reusableClosed closedOriginal && reusableClosed sourceType.closedType then
    closedSources.modify (·.insert key { closedOriginal, sourceType, rawKey })
  return rawKey

private def reusableCompletedHead (completed : CompletedHead) : Bool :=
  reusableClosed completed.closedHead && reusableClosed completed.liftedHead &&
    completed.state.helpers.all (fun (_, _, type, value) =>
      reusableClosed type && reusableClosed value) &&
    completed.state.checks.all (fun (argumentValue, etaValue, fValue) =>
      reusableClosed argumentValue && reusableClosed etaValue && reusableClosed fValue)

/-- Completed checks have exact closed endpoints and immutable source constants.
 Live generated helper definitions must retain the exact checked raw contents. -/
private def checkCompletedHead (completed : CompletedHead) : MetaM Unit := do
  phase "postprocess-cache-helpers"
  let env ← getEnv
  for (name, levels, type, value) in completed.state.helpers do
    let some (.defnInfo helper) := env.find? name | throwError "family.cache_helper_missing:{name}"
    unless helper.levelParams == levels && helper.type.equal type && helper.value.equal value &&
        helper.safety == .safe do
      throwError "family.cache_helper_changed:{name}"

def process (index : Nat) (row : Json) (scope : Name := .anonymous) :
    MetaM (Json × List Name) := do
  let stem := .str
    (if scope.isAnonymous then `K2HeadFamiliesPlaceholder else
      .str `K2HeadFamiliesPlaceholder scope.toString) s!"row{index}"
  let scopeLevels ← IO.ofExcept <|
    (← IO.ofExcept <| row.getObjVal? "levels").getArr? >>= fun values =>
      values.toList.mapM fun value => return (← value.getStr?).toName
  let part ← IO.ofExcept <| (← IO.ofExcept <| row.getObjVal? "part").getStr?
  let path ← IO.ofExcept <| (← IO.ofExcept <| row.getObjVal? "path").getArr? >>= fun values =>
    values.toList.mapM Json.getStr?
  withSource row fun info levels opened => do
    let xs := opened.xs
    let original := opened.node
    let (closedKey, closedEligible, closedOriginal, sourceType, cachedRawKey) ←
      prepareClosedSource scope scopeLevels levels opened
    let closedType := sourceType.closedType
    let originalHeadText ← IO.ofExcept <| (← IO.ofExcept <| row.getObjVal? "head").getStr?
    let key : CompletedHeadKey := (ExprStructEq.mk closedType,
      ExprStructEq.mk (mkConst `K2RawCoordinateLevels levels), xs.size, scopeLevels, scope)
    phase "postprocess-cache-lookup"
    let eligible := reusableClosed closedOriginal && reusableClosed closedType &&
      reusableClosed (mkConst `K2RawCoordinateLevels levels)
    let cached ← if eligible then do
      pure (((← completedHeads.get).find? (ExprStructEq.mk closedOriginal)).bind (fun entries => entries.find? key))
      else pure none
    let completed ← match cached with
      | some completed => do
          checkCompletedHead completed
          completedHeadReuse.modify fun (hits, misses) => (hits + 1, misses)
          pure completed
      | none => do
          completedHeadReuse.modify fun (hits, misses) => (hits, misses + 1)
          phase "postprocess-whnf"
          let normalized ← whnf original
          let closedHead ← lambdaClose xs normalized
          let startPath ← closingPath xs
          phase "postprocess-lift"
          let (lifted, state) ← (lift stem scopeLevels xs startPath normalized false).run {}
          let liftedHead ← lambdaClose xs lifted
          phase "postprocess-head-check"
          unless ← isDefEq closedOriginal liftedHead do throwError "family.head:{info.name}"
          let liftedHeadText ← if state.families.isEmpty then pure originalHeadText else constructorTerm liftedHead
          let completed : CompletedHead := {
            stem, closedHead, liftedHead, liftedHeadText,
            normalizedReferences := normalized.getUsedConstants.toList, state }
          if eligible && reusableCompletedHead completed then
            completedHeads.modify fun cache =>
              let entries := (cache.find? (ExprStructEq.mk closedOriginal)).getD {}
              cache.insert (ExprStructEq.mk closedOriginal) (entries.insert key completed)
          pure completed
    let actualStem := completed.stem
    let liftedHeadText := if completed.state.families.isEmpty then originalHeadText
      else completed.liftedHeadText
    let additionalReferences := completed.normalizedReferences ++ sourceType.references
    phase "postprocess-fresh-keys"
    let measured := Json.mkObj [
      ("rowIndex", toJson index), ("sourceCoordinate", row),
      ("placeholderStem", toJson actualStem),
      ("placeholderComponents", toJson (nameComponents actualStem)),
      ("levels", toJson scopeLevels),
      ("type", toJson (K2FactsGenerator.typeAt info.name part path levels)),
      ("head", toJson liftedHeadText),
      ("originalNormalizedHead", toJson originalHeadText),
      ("rawBindingKey", toJson (← completeClosedSource closedKey closedEligible
        closedOriginal sourceType levels cachedRawKey)),
      ("originalHeadKey", toJson (← K2FactsGenerator.rawBindingKey completed.closedHead closedType levels)),
      ("headKey", toJson (← K2FactsGenerator.rawBindingKey completed.liftedHead closedType levels)),
      ("additionalReferences", toJson additionalReferences),
      ("families", toJson completed.state.families),
      ("metaDefEqChecks", toJson "passed; generated Reg Exact evidence still requires compilation")]
    return (measured, additionalReferences)

/-- Add measurement keys and connected family helpers without changing the
 original raw coordinate, role, proof/data payload or binder-scope records. -/
def updateRow (scope : Name) (index : Nat) (row : Json) : MetaM (Json × List Name) := do
  let hasHead ← IO.ofExcept <| (← IO.ofExcept <| row.getObjVal? "hasHead").getBool?
  if hasHead then
    let (measured, references) ← process index row scope
    let families ← IO.ofExcept <| measured.getObjVal? "families"
    let hasFamilies := !(← IO.ofExcept families.getArr?).isEmpty
    let actualHead ← IO.ofExcept <| (if hasFamilies then measured else row).getObjVal? "head"
    let rawKey ← IO.ofExcept <| measured.getObjVal? "rawBindingKey"
    let headKey ← IO.ofExcept <| measured.getObjVal? "originalHeadKey"
    let additional ← IO.ofExcept <| measured.getObjVal? "additionalReferences"
    let actual := row.setObjVal! "rawBindingKey" rawKey
      |>.setObjVal! "headKey" headKey
      |>.setObjVal! "head" actualHead
      |>.setObjVal! "additionalReferences" additional
    return (if hasFamilies then actual.setObjVal! "headFamilies" measured else actual,
      references)
  let scopeLevels ← IO.ofExcept <|
    (← IO.ofExcept <| row.getObjVal? "levels").getArr? >>= fun values =>
      values.toList.mapM fun value => return (← value.getStr?).toName
  withSource row fun _ levels opened => do
    let (closedKey, closedEligible, closed, sourceType, cachedRawKey) ←
      prepareClosedSource scope scopeLevels levels opened
    phase "postprocess-fresh-keys"
    let key ← completeClosedSource closedKey closedEligible closed sourceType levels cachedRawKey
    let references := sourceType.references
    let actual := row.setObjVal! "rawBindingKey" (toJson key)
      |>.setObjVal! "headKey" (toJson key)
      |>.setObjVal! "additionalReferences" (toJson references)
    return (actual, references)


private structure OpeningFingerprint where
  closedNode : Expr
  closedType : Expr
  attributes : Array (Name × BinderInfo × LocalDeclKind × Option Bool)
  domains : Array Expr
  assigned : Array (Option Expr)
  instances : Array (Name × Nat)
  closing : List String

private def openingFingerprint (xs : Array Expr) (node : Expr) : MetaM OpeningFingerprint := do
  let lctx ← getLCtx
  let closedNode ← lambdaClose xs node
  let closedType ← typeClose xs (← K2FactsGenerator.inferNodeType node)
  let mut attributes := #[]
  let mut domains := #[]
  let mut assigned := #[]
  for index in [:xs.size] do
    let declaration := lctx.get! xs[index]!.fvarId!
    let binderPrefix := xs.extract 0 index
    let flag := match declaration with
      | .ldecl (nondep := flag) .. => some flag
      | _ => none
    attributes := attributes.push
      (declaration.userName, declaration.binderInfo, declaration.kind, flag)
    domains := domains.push (← lambdaClose binderPrefix declaration.type)
    let value ← match declaration.value? (allowNondep := true) with
      | some value => pure (some (← lambdaClose binderPrefix value))
      | none => pure none
    assigned := assigned.push value
  let mut instances := #[]
  for localInstance in ← getLocalInstances do
    unless localInstance.fvar.isFVar && (lctx.find? localInstance.fvar.fvarId!).isSome do
      throwError "opening_control.instance_outside_lctx"
    let some position := xs.findIdx? (fun sourceVar => sourceVar.equal localInstance.fvar) |
      throwError "opening_control.instance_outside_telescope"
    instances := instances.push (localInstance.className, position)
  let closeEdges ← closingPath xs
  return {
    closedNode := closedNode
    closedType := closedType
    attributes := attributes
    domains := domains
    assigned := assigned
    instances := instances
    closing := closeEdges }

private def OpeningFingerprint.rawEqual (left right : OpeningFingerprint) : Bool :=
  left.closedNode.equal right.closedNode && left.closedType.equal right.closedType &&
  left.attributes == right.attributes && left.instances == right.instances &&
  left.closing == right.closing && left.domains.size == right.domains.size &&
  (left.domains.zip right.domains).all (fun (first, second) => first.equal second) &&
  left.assigned.size == right.assigned.size &&
  (left.assigned.zip right.assigned).all (fun (first, second) => match first, second with
    | none, none => true
    | some first, some second => first.equal second
    | _, _ => false)

/-- Temporary raw opening control; no result is imported by generated Reg. -/
def validateSourceOpening (row : Json) : MetaM Unit := do
  let name ← IO.ofExcept <| decodeName (← IO.ofExcept <| row.getObjVal? "declarationComponents")
  let some info := (← getEnv).find? name | throwError "opening_control.source_missing:{name}"
  let part ← IO.ofExcept <| (← IO.ofExcept <| row.getObjVal? "part").getStr?
  let path ← IO.ofExcept <| (← IO.ofExcept <| row.getObjVal? "path").getArr? >>= fun values =>
    values.toList.mapM Json.getStr?
  let levels ← IO.ofExcept <| (← IO.ofExcept <| row.getObjVal? "coordinateLevelTrees").getArr? >>= fun values =>
    values.toList.mapM decodeLevel
  let original ← if part == "type" then pure info.type else
    match info with
    | .defnInfo definition => pure definition.value
    | _ => throwError "opening_control.source_value:{name}"
  let original := if levels == info.levelParams.map Level.param then original else
    LeanInformationAudit.Contract.Literal.instantiateRawLevels info.levelParams levels original
  let fresh ← atSource original path #[] openingFingerprint
  let cached ← withSource row fun _ _ opened => openingFingerprint opened.xs opened.node
  let repeated ← withSource row fun _ _ opened => openingFingerprint opened.xs opened.node
  unless fresh.rawEqual cached && cached.rawEqual repeated do
    throwError "opening_control.raw_mismatch:{name}:{part}:{path}"
  let first ← withSource row fun _ _ opened => pure opened
  let second ← withSource row fun _ _ opened => pure opened
  unless first.node.equal second.node && first.xs.size == second.xs.size &&
      first.contextID == second.contextID && first.eligible == second.eligible &&
      (first.xs.zip second.xs).all (fun (left, right) => left.equal right) do
    throwError "opening_control.repeated_frame_changed:{name}:{part}:{path}"
  IO.println s!"opening_control_passed {name} part={part} path={path} telescope={fresh.attributes.size} instances={fresh.instances.size}"

/-- Temporary exact closure/context controls in the existing opening executable. -/
def validateClosedSourceReuse : MetaM Unit := do
  resetCompletedHeads
  K2FactsGenerator.rawBindingKeys.set {}
  let parent ← captureRootSource (mkApp (mkConst ``List [.zero]) (mkConst ``Nat))
  unless parent.contextID == 0 && parent.eligible do
    throwError "closed_source_control.empty_root"
  let openArgument := withLCtx parent.lctx parent.localInstances <|
    atSource parent.node ["argument"] parent.xs (captureChildSource parent false)
  let first ← openArgument
  let second ← openArgument
  unless first.contextID == parent.contextID && second.contextID == first.contextID &&
      first.node.equal second.node do
    throwError "closed_source_control.nonbinder_context"
  let inspect := fun (opened : OpenedSource) (levels : List Level)
      (scopeLevels : List Name) (scope : Name) =>
    withLCtx opened.lctx opened.localInstances do
      let (key, eligible, closedOriginal, sourceType, cachedRawKey) ←
        prepareClosedSource scope scopeLevels levels opened
      let rawKey ← completeClosedSource key eligible closedOriginal sourceType levels cachedRawKey
      return ({ closedOriginal, sourceType, rawKey } : ClosedSource)
  let firstResult ← inspect first [] [] `K2ClosedSourceControl
  let secondResult ← inspect second [] [] `K2ClosedSourceControl
  unless firstResult.closedOriginal.equal secondResult.closedOriginal &&
      firstResult.sourceType.closedType.equal secondResult.sourceType.closedType &&
      firstResult.sourceType.references == secondResult.sourceType.references &&
      firstResult.rawKey == secondResult.rawKey && (← closedSourceReuse.get) == (1, 1) do
    throwError "closed_source_control.exact_hit"
  let frameX ← withLocalDecl `x .default (mkConst ``Nat) fun x =>
    captureChildSource parent true #[x] (mkConst ``Nat)
  let frameY ← withLocalDecl `y .default (mkConst ``Nat) fun y =>
    captureChildSource parent true #[y] (mkConst ``Nat)
  let frameBool ← withLocalDecl `x .default (mkConst ``Bool) fun x =>
    captureChildSource parent true #[x] (mkConst ``Nat)
  let frameLet0 ← withLetDecl `z (mkConst ``Nat) (mkNatLit 0) fun z =>
    captureChildSource parent true #[z] (mkConst ``Nat)
  let frameLet1 ← withLetDecl `z (mkConst ``Nat) (mkNatLit 1) fun z =>
    captureChildSource parent true #[z] (mkConst ``Nat)
  let frames := #[frameX, frameY, frameBool, frameLet0, frameLet1]
  for index in [:frames.size] do
    unless frames[index]!.contextID != parent.contextID && frames[index]!.eligible do
      throwError "closed_source_control.bound_context"
    for prior in [:index] do
      unless frames[index]!.contextID != frames[prior]!.contextID do
        throwError "closed_source_control.context_alias"
  let xResult ← inspect frameX [] [] `K2ClosedSourceControl
  let yResult ← inspect frameY [] [] `K2ClosedSourceControl
  let boolResult ← inspect frameBool [] [] `K2ClosedSourceControl
  let let0Result ← inspect frameLet0 [] [] `K2ClosedSourceControl
  let let1Result ← inspect frameLet1 [] [] `K2ClosedSourceControl
  unless !xResult.closedOriginal.equal yResult.closedOriginal &&
      !xResult.sourceType.closedType.equal yResult.sourceType.closedType &&
      !xResult.closedOriginal.equal boolResult.closedOriginal &&
      !xResult.sourceType.closedType.equal boolResult.sourceType.closedType &&
      !let0Result.closedOriginal.equal let1Result.closedOriginal &&
      !let0Result.sourceType.closedType.equal let1Result.sourceType.closedType &&
      xResult.rawKey != yResult.rawKey && xResult.rawKey != boolResult.rawKey &&
      let0Result.rawKey != let1Result.rawKey do
    throwError "closed_source_control.raw_frame_distinctions"
  let levelsResult ← inspect first [.param `u] [] `K2ClosedSourceControl
  unless levelsResult.rawKey != firstResult.rawKey do
    throwError "closed_source_control.raw_levels"
  let scopeLevelsResult ← inspect first [] [`u] `K2ClosedSourceControl
  let scopeResult ← inspect first [] [] `K2ClosedSourceControlOther
  unless scopeLevelsResult.rawKey == firstResult.rawKey &&
      scopeResult.rawKey == firstResult.rawKey && (← closedSourceReuse.get) == (1, 9) do
    throwError "closed_source_control.scope_miss"
  let nodeMVar ← mkFreshExprMVar (some (mkConst ``Nat))
  let nodeFrame ← captureRootSource nodeMVar
  let valueFrame ← withLetDecl `z (mkConst ``Nat) nodeMVar fun z =>
    captureChildSource parent true #[z] (mkConst ``Nat)
  let domainMVar ← mkFreshExprMVar (some (mkSort (.succ .zero)))
  let domainFrame ← withLocalDecl `x .default domainMVar fun x =>
    captureChildSource parent true #[x] (mkConst ``Nat)
  unless !nodeFrame.eligible && !valueFrame.eligible && !domainFrame.eligible do
    throwError "closed_source_control.metavariable_eligibility"
  resetCompletedHeads
  unless (← closedSources.get).isEmpty && (← closedSourceReuse.get) == (0, 0) &&
      (← sourceContextIDs.get) == 1 do
    throwError "closed_source_control.reset"
  K2FactsGenerator.rawBindingKeys.set {}
  IO.println "closed_source_control exact_context_binders_lets_levels_scopes_mvars_reset=passed"

end K2HeadFamiliesGenerator
