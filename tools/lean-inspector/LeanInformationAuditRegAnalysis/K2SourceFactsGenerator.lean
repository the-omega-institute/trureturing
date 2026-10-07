import Lean
import LeanInformationAuditInterface.Contract.NodeFacts

open Lean Meta
open LeanInformationAudit.Contract

namespace K2SourceFactsGenerator

private def family := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily
private def refValue (input : Expr) : MetaM Expr := do
  let value ← whnf input
  unless value.getAppFn.isConstOf ``Ref.mk do throwError "expected Ref: {value}"
  return value.getAppArgs.back!

private def optional (input : Expr) : MetaM (Option Expr) := do
  let value ← whnf input
  if value.isAppOfArity ``Option.none 1 then return none
  unless value.isAppOfArity ``Option.some 2 do throwError "expected Option: {value}"
  return some value.getAppArgs[1]!

private def recordFields (input : Expr) (count : Nat) : MetaM (Array Expr) := do
  let value ← whnf input
  let .const name _ := value.getAppFn | throwError "record head: {value}"
  let .ctorInfo ctor ← getConstInfo name | throwError "record constructor: {value}"
  let args := value.getAppArgs
  unless args.size == ctor.numParams + count do throwError "record arity {name}"
  return args.extract ctor.numParams args.size

private def text (e : Expr) : MetaM String := do
  return (← ppExpr e).pretty 120

private def ownerOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.header.modules[index.toNat]!.module
  | none => env.mainModule

private def instantiateRawLevels (params : List Name) (levels : List Level) (e : Expr) : Expr :=
  let rec level : Level → Level
    | .param name => ((params.zip levels).find? (fun pair => pair.1 == name)).map (·.2)
        |>.getD (.param name)
    | .succ value => .succ (level value)
    | .max left right => .max (level left) (level right)
    | .imax left right => .imax (level left) (level right)
    | other => other
  e.replace fun expression => match expression with
    | .const name levels => some (.const name (levels.map level))
    | .sort universeLevel => some (.sort (level universeLevel))
    | _ => none

private def levelText : Level → MetaM String
  | .zero => pure ".zero"
  | .param name => pure ("(.param `" ++ name.toString ++ ")")
  | .succ level => return "(.succ " ++ (← levelText level) ++ ")"
  | .max left right => return "(.max " ++ (← levelText left) ++ " " ++ (← levelText right) ++ ")"
  | .imax left right => return "(.imax " ++ (← levelText left) ++ " " ++ (← levelText right) ++ ")"
  | .mvar _ => throwError "coordinate universe metavariable"

private partial def nameComponents : Name → List Json
  | .anonymous => []
  | .str namePrefix component => nameComponents namePrefix ++ [.str component]
  | .num namePrefix component => nameComponents namePrefix ++ [toJson component]

private partial def levelTree : Level → Json
  | .zero => toJson #[Json.str "zero"]
  | .param name => toJson #[Json.str "param", toJson (nameComponents name)]
  | .succ nested => toJson #[Json.str "succ", levelTree nested]
  | .max left right => toJson #[Json.str "max", levelTree left, levelTree right]
  | .imax left right => toJson #[Json.str "imax", levelTree left, levelTree right]
  | .mvar _ => panic! "coordinate universe metavariable"

private structure CoordinateAddress where
  code : String
  declarationComponents : List Json
  part : String
  path : List String
  coordinateLevelTrees : List Json
  deriving ToJson

private def coord (owner declaration : Name) (part : String) (path : List String)
    (levels : List Level) : MetaM CoordinateAddress := do
  let levelTexts ← levels.mapM levelText
  let code := "{ owner := `" ++ owner.toString ++ ", declaration := `" ++ declaration.toString ++
    ", part := ." ++ part ++ ", path := [" ++ String.intercalate ", " (path.map ("." ++ ·)) ++
    "], levels := [" ++ String.intercalate ", " levelTexts ++ "] }"
  return {
    code := code
    declarationComponents := nameComponents declaration
    part := part
    path := path
    coordinateLevelTrees := levels.map levelTree }

private def declaration (name : Name) (levels : List Name) : String :=
  name.toString ++ if levels.isEmpty then "" else
    ".{" ++ String.intercalate ", " (levels.map Name.toString) ++ "}"

private def helper (name : Name) (levels : List Name) (value : Expr) : MetaM String := do
  check value
  return "noncomputable def " ++ declaration name levels ++ " : " ++
    (← text (← inferType value)) ++ " :=\n  " ++ (← text value) ++ "\n"

private def named (name : Name) (levels : List Level) : String :=
  "(@" ++ name.toString ++ (if levels.isEmpty then "" else
    ".{" ++ String.intercalate ", " (levels.map toString) ++ "}") ++ ")"

private partial def list (input : Expr) : MetaM (Array Expr) := do
  let value ← whnf input
  if value.isAppOfArity ``List.nil 1 then return #[]
  unless value.isAppOfArity ``List.cons 3 do throwError "not a finite list: {value}"
  return #[value.getAppArgs[1]!] ++ (← list value.getAppArgs[2]!)

private def finiteIndices (dictionary : Expr) : MetaM (Array Expr) := do
  let elems ← whnf (.proj `Fintype 0 dictionary)
  let multiset ← whnf (.proj `Finset 0 elems)
  unless multiset.isAppOfArity ``Quot.mk 3 do throwError "not finite dictionary"
  list multiset.getAppArgs[2]!

private partial def packedAt (type : Expr) (values : Array Expr) (index depth : Nat) :
    MetaM (Expr × Nat) := do
  if depth > 256 then throwError "source parameter packing depth"
  if let some value := values[index]? then
    if ← isDefEq (← inferType value) type then return (value, index + 1)
  if (← isClass? type).isSome || (← isProp type) then
    for localDecl in (← getLCtx) do
      if ← isDefEq localDecl.type type then return (mkFVar localDecl.fvarId, index)
    throwError "source parameter local field absent: {type}"
  let type ← whnf type
  let .const name levels := type.getAppFn
    | throwError "source parameter field type: {type}"
  let .inductInfo inductiveInfo ← getConstInfo name
    | throwError "source parameter constructor type: {type}"
  let [constructorName] := inductiveInfo.ctors
    | throwError "source parameters require one constructor: {type}"
  let .ctorInfo constructorInfo ← getConstInfo constructorName
    | throwError "source parameter constructor absent: {constructorName}"
  unless constructorInfo.levelParams.length == levels.length do
    throwError "source parameter constructor universe arity: {constructorName}"
  let mut result := mkConst constructorName levels
  let mut constructorType := instantiateRawLevels constructorInfo.levelParams levels constructorInfo.type
  let arguments := type.getAppArgs
  for ordinal in [:inductiveInfo.numParams] do
    let some parameter := arguments[ordinal]?
      | throwError "source parameter constructor arguments: {type}"
    let .forallE _ _ body _ := constructorType
      | throwError "source parameter constructor telescope: {constructorName}"
    result := mkApp result parameter
    constructorType := body.instantiate1 parameter
  let mut next := index
  for _ in [:constructorInfo.numFields] do
    let .forallE _ domain body _ ← whnf constructorType
      | throwError "source parameter field telescope: {constructorName}"
    let (field, remaining) ← packedAt domain values next (depth + 1)
    result := mkApp result field
    constructorType := body.instantiate1 field
    next := remaining
  unless ← isDefEq (← inferType result) type do
    throwError "source parameter constructed type: {type}"
  return (result, next)

private def packed (type : Expr) (values : Array Expr) : MetaM Expr := do
  let (result, used) ← packedAt type values 0 0
  unless used == values.size do
    throwError "source parameter unused coordinates: used={used}; selected={values.size}; type={type}"
  return result

private partial def operandAt (input : Expr) : List String → MetaM Expr
  | [] => pure input
  | edge :: rest =>
    match input, edge with
    | .app f _, "fn" => operandAt f rest
    | .app _ a, "arg" => operandAt a rest
    | _, _ => throwError "state operand shape {edge}: {input}"

private partial def atPath (input : Expr) (xs : Array Expr) (path : List String)
    (k : Array Expr → Expr → MetaM α) : MetaM α := do
  match path with
  | [] => k xs input
  | edge :: rest =>
    match input, edge with
    | .app f _, "fn" => atPath f xs rest k
    | .app _ a, "arg" => atPath a xs rest k
    | .forallE _ domain _ _, "domain" | .lam _ domain _ _, "domain" => atPath domain xs rest k
    | .forallE n domain body bi, "body" | .lam n domain body bi, "body" =>
      withLocalDecl n bi domain fun x => atPath (body.instantiate1 x) (xs.push x) rest k
    | .letE _ type _ _ _, "type" => atPath type xs rest k
    | .letE _ _ value _ _, "value" => atPath value xs rest k
    | .letE n type value body nd, "body" =>
      withLetDecl n type value (nondep := nd) fun x => atPath (body.instantiate1 x) (xs.push x) rest k
    | .mdata _ body, "body" | .proj _ _ body, "body" => atPath body xs rest k
    | _, _ => throwError "source path shape {edge}: {input}"

private partial def coordinatePath (input : Expr) : List String → MetaM (List String)
  | [] => pure []
  | edge :: rest => do
    let (name, child) ← match input, edge with
      | .app f _, "fn" => pure ("function", f)
      | .app _ a, "arg" => pure ("argument", a)
      | .forallE _ t _ _, "domain" | .lam _ t _ _, "domain" => pure ("domain", t)
      | .forallE _ _ b _, "body" | .lam _ _ b _, "body" => pure ("body", b)
      | .letE _ t _ _ _, "type" => pure ("letType", t)
      | .letE _ _ v _ _, "value" => pure ("letValue", v)
      | .letE _ _ _ b _, "body" => pure ("letBody", b)
      | .mdata _ b, "body" => pure ("metadata", b)
      | .proj _ _ b, "body" => pure ("projection", b)
      | _, _ => throwError "source coordinate shape {edge}: {input}"
    return name :: (← coordinatePath child rest)

private def close (xs : Array Expr) (e : Expr) : MetaM Expr :=
  mkLambdaFVars xs e (usedOnly := false) (usedLetOnly := false)
    (etaReduce := false) (generalizeNondepLet := false)

private def enumeration (name : Name) (levels : List Name) (carrier : Expr)
    (values : Array Expr) : MetaM String := do
  let values ← values.mapM text
  return "noncomputable def " ++ declaration name levels ++
    " : LeanInformationAudit.Contract.FiniteEnumeration (" ++ (← text carrier) ++ ") where\n" ++
    "  values := [" ++ String.intercalate ", " values.toList ++ "]\n" ++
    "  nodup := by decide +kernel\n  complete := by decide +kernel\n"

private structure Observation where
  code : String
  fact : Option Name
  definitionallyEqual : Bool
  error : Option String := none
  coordinateAddresses : Array CoordinateAddress := #[]
  deriving ToJson

private inductive AliasClosure where
  | mk (term : Expr) (bindings : List AliasClosure)

private def canonicalOperand (initial : Expr) : MetaM Expr := do
  let mut owner := initial
  let mut current := AliasClosure.mk initial []
  let mut arguments : List AliasClosure := []
  for _ in [:4096] do
    let .mk term bindings := current
    match term with
    | .mdata data body =>
      if data.contains `LeanInformationAudit.arenaConstruction then return owner
      if data.contains `LeanInformationAudit.arenaSourceUnsupported then
        throwError "unsupported canonical arena {initial}"
      current := .mk body bindings
    | .app f a =>
      arguments := .mk a bindings :: arguments
      current := .mk f bindings
    | .letE _ _ value body _ => current := .mk body (.mk value bindings :: bindings)
    | .lam _ _ body _ =>
      match arguments with
      | [] => return owner
      | arg :: rest =>
        arguments := rest
        current := .mk body (arg :: bindings)
    | .bvar index =>
      match bindings with
      | [] => throwError "open canonical arena {initial}"
      | value :: rest =>
        current := if index == 0 then value else .mk (.bvar (index - 1)) rest
    | .const name levels =>
      if arguments.isEmpty then owner := term
      match (← getEnv).find? name with
      | some (.defnInfo info) =>
        current := .mk (instantiateRawLevels info.levelParams levels info.value) []
      | _ => return owner
    | _ => return owner
  throwError "canonical arena work exceeded {initial}"

private structure CanonicalFacts where
  code : String := ""
  names : Array Name := #[]
  arena : Name := .anonymous
  objectArena : Name := .anonymous
  coordinateAddresses : Array CoordinateAddress := #[]

private def canonicalFacts (module : Name) (info : ConstantInfo)
    (fields : Array Expr) : MetaM CanonicalFacts := do
  let mut result : CanonicalFacts := {}
  for index in #[4, 5] do
    let arenaRef ← whnf fields[index]!
    let raw ← refValue arenaRef.getAppArgs.back!
    let canonical ← canonicalOperand raw
    let .const name _ := canonical.getAppFn | throwError "unnamed canonical arena {canonical}"
    let role := if index == 4 then "arena" else "object_arena"
    let valueName := info.name.str ("__k2_canonical_" ++ role)
    let factName := info.name.str ("__k2_canonical_" ++ role ++ "_fact")
    let leftAt ← coord module info.name "value"
      (List.replicate (25 - index - 1) "function" ++ ["argument", "argument", "argument"])
      (info.levelParams.map Level.param)
    let rightAt ← coord module valueName "value" [] (info.levelParams.map Level.param)
    result := { result with
      code := result.code ++ (← helper valueName info.levelParams canonical) ++
        "noncomputable def " ++ declaration factName info.levelParams ++
        " : LeanInformationAudit.Contract.NodeFact := .exact\n  (" ++ (← text raw) ++
        ") (" ++ (← text canonical) ++ ")\n  " ++ leftAt.code ++ "\n  " ++ rightAt.code ++
        "\n  .evidence\n"
      names := result.names.push factName
      coordinateAddresses := result.coordinateAddresses ++ #[leftAt, rightAt]
      arena := if index == 4 then name else result.arena
      objectArena := if index == 5 then name else result.objectArena }
  return result

private def observation (module inputName : Name) (levels : List Name) (sourceLevels : List Level)
    (sourceName : Name) (sourcePart : String) (source : Expr) (selection : SourceSelection)
    (actual params : Expr) (roles : Array Expr) (index : Nat) : MetaM Observation := do
  let some selected := selection.readouts[index]? | throwError "source readout index {index}"
  let path := match selection.definition with
    | none => selected.path
    | some definition => selected.path.extract definition.path.size selected.path.size
  atPath source #[] path.toList fun xs original => do
    let parameter ← packed params (selection.coordinates.map fun ordinal => xs[ordinal]!)
    let mut observed ← mkAppM (family ++ `Realization.readout) #[actual, roles[index]!, parameter]
    unless selected.functionOperand do
      let state ← match selected.stateOperand with
        | none => pure xs[selected.stateBinder]!
        | some path => operandAt original path.toList
      checkApp observed state
      observed := mkApp observed state
    let left ← close xs original
    let right ← close xs observed
    check left
    unless selected.booleanPredicate do
      let sourceType ← inferType left
      let readoutType ← inferType right
      unless ← isDefEq sourceType readoutType do
        throwError "source observation output carrier mismatch:\nsource type: {sourceType}\nreadout type: {readoutType}"
    let rightName := inputName.str s!"__k2_observation_{index}"
    let factName := inputName.str s!"__k2_observation_fact_{index}"
    let env ← getEnv
    let leftAt ← coord (ownerOf env sourceName) sourceName sourcePart
      (← coordinatePath source path.toList) sourceLevels
    let rightAt ← coord module rightName "value" [] (levels.map Level.param)
    let mut code ← helper rightName levels right
    let equal ← isDefEq left right
    if selected.booleanPredicate then
      let type := mkApp2 (mkConst `LeanInformationAudit.Contract.BoolReflection) original observed
      let closedType ← mkForallFVars xs type (usedOnly := false) (usedLetOnly := false)
        (generalizeNondepLet := false)
      check closedType
      let placeholder ← close xs (mkConst `K2_SOURCE_REFLECTION_BODY)
      let body := "{ sourceAt := " ++ leftAt.code ++ ", readoutAt := " ++ rightAt.code ++
        ", reflects := by change (_ ↔ decide (_ : Prop) = true); simp only [decide_eq_true_eq] }"
      let proof := (← text placeholder).replace "K2_SOURCE_REFLECTION_BODY" body
      code := code ++ "noncomputable def " ++ declaration factName levels ++ " : " ++
        (← text closedType) ++ " :=\n  " ++ proof ++ "\n"
    else
      code := code ++ "noncomputable def " ++ declaration factName levels ++
        " : LeanInformationAudit.Contract.NodeFact := .equal\n  (" ++ (← text left) ++
        ") (" ++ (← text right) ++ ")\n  " ++ leftAt.code ++ "\n  " ++ rightAt.code ++
        "\n  (by first | rfl | (ext <;> rfl))\n"
    return {
      code := code
      fact := some factName
      definitionallyEqual := equal
      coordinateAddresses := #[leftAt, rightAt] }

private unsafe def sourceRow (module : Name) (info : ConstantInfo)
    (fields : Array Expr) (canonical : CanonicalFacts) (sourceBound : Bool)
    (canonicalRegistryArena : Name) : MetaM Json := do
  let selected ← optional fields[16]!
  let some selected := selected | return Json.mkObj [
    ("module", toJson module), ("inputName", toJson info.name), ("code", toJson canonical.code),
    ("canonicalArena", toJson canonical.arena), ("canonicalObjectArena", toJson canonical.objectArena),
    ("canonicalRegistryArena", toJson canonicalRegistryArena),
    ("relationFactNames", toJson canonical.names),
    ("coordinateAddresses", toJson canonical.coordinateAddresses)]
  let selection ← evalExpr SourceSelection (← inferType selected) selected
  let implementation ← whnf fields[8]!
  let args := implementation.getAppArgs
  let record ← if sourceBound then refValue args[2]! else do
    let some family ← optional fields[18]! | throwError "source selection without family"
    let sigma ← recordFields family 2
    refValue sigma[1]!
  let recordType ← inferType record
  unless recordType.isAppOfArity (family ++ `Registration) 2 do throwError "family record type"
  let arena := recordType.getAppArgs[0]!
  let actual ← mkAppM (family ++ `Registration.actual) #[record]
  let recordInfo ← getConstInfo record.constName!
  let recordValue := instantiateRawLevels recordInfo.levelParams record.constLevels!
    (recordInfo.value?.getD recordInfo.type)
  unless recordValue.isAppOfArity (family ++ `Registration.mk) 7 do
    throwError "source record literal {recordInfo.name}"
  let rawActual := recordValue.getAppArgs[2]!
  let signature ← mkAppM (family ++ `Arena.signature) #[arena]
  let params ← mkAppM (family ++ `Signature.Params) #[signature]
  let roleType ← whnf (← mkAppM (family ++ `Signature.Role) #[signature])
  let anchorType ← whnf (← mkAppM (family ++ `Signature.Anchor) #[signature])
  let roles ← finiteIndices (← mkAppM (family ++ `Signature.finiteRole) #[signature])
  let anchors ← finiteIndices (← mkAppM (family ++ `Signature.finiteAnchor) #[signature])
  unless roles.size == selection.readouts.size do throwError "source roles mismatch {info.name}"
  let original := info.type.getAppArgs[1]!
  let originalInfo ← getConstInfo original.constName!
  let originalType := instantiateRawLevels originalInfo.levelParams original.constLevels! originalInfo.type
  let (sourceName, sourcePart, source) ← match selection.definition with
    | none => pure (originalInfo.name, "type", originalType)
    | some definition =>
      let sourceInfo ← getConstInfo definition.name
      let some value := sourceInfo.value? | throwError "source definition absent"
      unless sourceInfo.levelParams.length == original.constLevels!.length do
        throwError "source definition universe arity {definition.name}"
      pure (definition.name, "value", instantiateRawLevels sourceInfo.levelParams original.constLevels! value)
  let levels := info.levelParams
  let law ← mkAppM (family ++ `Arena.Law) #[arena, actual]
  let lawName := info.name.str "__k2_law"
  let bridgeFact := info.name.str "__k2_bridge_fact"
  let env ← getEnv
  let originalAt ← coord (ownerOf env originalInfo.name) originalInfo.name "type" [] original.constLevels!
  let lawAt ← coord module lawName "value" [] (levels.map Level.param)
  let mut code := canonical.code ++ (← helper lawName levels law)
  code := code ++ "noncomputable def " ++ declaration bridgeFact levels ++
    " : LeanInformationAudit.Contract.NodeFact := .equivalent\n  (" ++ (← text originalType) ++
    ") (" ++ (← text law) ++ ")\n  " ++ originalAt.code ++ "\n  " ++ lawAt.code ++
    "\n  (" ++ (← text (← mkAppM (family ++ `Registration.bridge) #[record])) ++ ")\n"
  let roleName := info.name.str "__k2_roles"
  let anchorName := info.name.str "__k2_anchors"
  code := code ++ (← enumeration roleName levels roleType roles) ++
    (← enumeration anchorName levels anchorType anchors)
  let observations ← (List.range selection.readouts.size).toArray.mapM fun index => do
    try
      observation module info.name levels original.constLevels! sourceName sourcePart source selection
        rawActual params roles index
    catch error => do
      let reason ← error.toMessageData.toString
      return { code := "", fact := none, definitionallyEqual := false, error := some reason }
  code := code ++ String.join (observations.toList.map (·.code))
  let mut coordinateAddresses := canonical.coordinateAddresses ++ #[originalAt, lawAt] ++
    (observations.foldl (fun addresses observation => addresses ++ observation.coordinateAddresses) #[])
  let arenaFields ← recordFields arena 2
  let lawFunction := arenaFields[1]!
  let lawFunctionName := info.name.str "__k2_law_function"
  let exclusionName := info.name.str "__k2_exclusion"
  code := code ++ (← helper lawFunctionName levels lawFunction)
  let lawFunctionAt ← coord module lawFunctionName "value" [] (levels.map Level.param)
  let recordText ← text record
  code := code ++ "noncomputable def " ++ declaration exclusionName levels ++
    " : LeanInformationAudit.Contract.StatementExclusion (" ++ (← text lawFunction) ++
    ") (" ++ (← text originalType) ++ ") where\n  lawLocation := " ++ lawFunctionAt.code ++
    "\n  statementLocation := " ++ originalAt.code ++
    "\n  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (" ++ recordText ++ ").actual " ++
    "(" ++ recordText ++ ").variation.2.choose (" ++ recordText ++
    ").variation.1 (" ++ recordText ++ ").variation.2.choose_spec\n"
  coordinateAddresses := coordinateAddresses ++ #[lawFunctionAt, originalAt]
  let descriptor ← optional fields[11]!
  let descriptorFact := info.name.str "__k2_descriptor_fact"
  let mut relations := canonical.names ++ #[bridgeFact] ++ observations.filterMap (·.fact)
  let mut descriptorDefEq := true
  if let some descriptor := descriptor then
    let leftAt ← coord module info.name "value"
      (List.replicate (25 - 11 - 1) "function" ++ ["argument", "argument"])
      (levels.map Level.param)
    let rightAt ← coord (ownerOf env recordInfo.name) recordInfo.name "value"
      (List.replicate 4 "function" ++ ["argument"]) record.constLevels!
    descriptorDefEq ← isDefEq descriptor rawActual
    code := code ++ "noncomputable def " ++ declaration descriptorFact levels ++
      " : LeanInformationAudit.Contract.NodeFact := .equal\n  (" ++ (← text descriptor) ++
      ") (" ++ (← text rawActual) ++ ")\n  " ++ leftAt.code ++ "\n  " ++ rightAt.code ++
      "\n  (by first | rfl | (ext <;> rfl))\n"
    relations := relations.push descriptorFact
    coordinateAddresses := coordinateAddresses ++ #[leftAt, rightAt]
  let mut finiteLift : Option Name := none
  if !sourceBound then
    let finiteArena := args[1]!
    let familyPrefix := arena.getAppFn.constName!.getPrefix
    let lift := familyPrefix ++ `fromLegacy
    let lower := familyPrefix ++ `toLegacy
    unless (env.find? lift).isSome && (env.find? lower).isSome do
      throwError "finite lift construction absent {familyPrefix}"
    let liftName := info.name.str "__k2_finite_lift"
    let liftText := named lift arena.getAppFn.constLevels!
    let lowerText := named lower arena.getAppFn.constLevels!
    code := code ++ "noncomputable def " ++ declaration liftName levels ++
      " : LeanInformationAudit.Contract.FiniteLiftFacts (" ++ (← text finiteArena) ++
      ") (" ++ (← text arena) ++ ") " ++ liftText ++ " " ++ lowerText ++ " where\n" ++
      "  lowerLift := " ++ (familyPrefix ++ `to_from_legacy).toString ++ "\n" ++
      "  liftLower := " ++ (familyPrefix ++ `from_to_legacy).toString ++ "\n" ++
      "  law := by intro r; rw [" ++ (familyPrefix ++ `full_law_transport).toString ++
      ", " ++ (familyPrefix ++ `to_from_legacy).toString ++ "]\n  observations := []\n"
    let finiteActual ← refValue args[4]!
    let finiteActualType ← inferType finiteActual
    unless finiteActualType.isAppOfArity
        `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization 3 do
      throwError "finite lift bridge type {info.name}"
    let liftedActual := mkApp (mkConst lift arena.getAppFn.constLevels!)
      finiteActualType.getAppArgs[2]!
    let actualLiftName := info.name.str "__k2_lifted_actual"
    let actualFactName := info.name.str "__k2_lifted_actual_fact"
    code := code ++ (← helper actualLiftName levels liftedActual)
    let actualAt ← coord (ownerOf env recordInfo.name) recordInfo.name "value"
      (List.replicate 4 "function" ++ ["argument"]) record.constLevels!
    let liftedAt ← coord module actualLiftName "value" [] (levels.map Level.param)
    code := code ++ "noncomputable def " ++ declaration actualFactName levels ++
      " : LeanInformationAudit.Contract.NodeFact := .equal\n  (" ++ (← text rawActual) ++
      ") (" ++ (← text liftedActual) ++ ")\n  " ++ actualAt.code ++ "\n  " ++ liftedAt.code ++
      "\n  (by first | rfl | (ext <;> rfl))\n"
    relations := relations.push actualFactName
    coordinateAddresses := coordinateAddresses ++ #[actualAt, liftedAt]
    finiteLift := some liftName
  let observationErrors := observations.mapIdx fun index item => (index, item.error)
  let observationErrors := observationErrors.filter (·.2.isSome)
  return Json.mkObj [
    ("module", toJson module), ("inputName", toJson info.name), ("code", toJson code),
    ("exclusion", toJson exclusionName), ("finiteLift", toJson finiteLift),
    ("roleEnumeration", toJson roleName), ("anchorEnumeration", toJson anchorName),
    ("canonicalArena", toJson canonical.arena), ("canonicalObjectArena", toJson canonical.objectArena),
    ("canonicalRegistryArena", toJson canonicalRegistryArena),
    ("relationFactNames", toJson relations), ("observations", toJson observations),
    ("observationErrors", toJson observationErrors),
    ("descriptorDefEq", toJson descriptorDefEq),
    ("coordinateAddresses", toJson coordinateAddresses)]

unsafe def row (module : Name) (info : ConstantInfo) : MetaM Json := do
  let fields ← recordFields (info.value?.getD info.type) 20
  let canonical ← canonicalFacts module info fields
  let sourceBound := (← whnf fields[8]!).getAppFn.isConstOf ``Implementation.source
  let localNames ← whnf fields[7]!
  let canonicalRegistryArena := if sourceBound || localNames.isConstOf ``Bool.false then
      canonical.objectArena else canonical.arena
  try
    sourceRow module info fields canonical sourceBound canonicalRegistryArena
  catch error =>
    return Json.mkObj [
      ("module", toJson module), ("inputName", toJson info.name),
      ("code", toJson canonical.code),
      ("canonicalArena", toJson canonical.arena),
      ("canonicalObjectArena", toJson canonical.objectArena),
      ("canonicalRegistryArena", toJson canonicalRegistryArena),
      ("relationFactNames", toJson canonical.names),
      ("coordinateAddresses", toJson canonical.coordinateAddresses),
      ("sourceFactError", toJson (← error.toMessageData.toString))]

unsafe def collect (module : Name) (selectedInputs : Option (Array ConstantInfo) := none) : MetaM Json := do
  let env ← getEnv
  let inputs : Array ConstantInfo := match selectedInputs with
    | some inputs => inputs
    | none =>
      let infos : List (Name × ConstantInfo) := env.constants.toList
      let owned := infos.filter (fun pair => ownerOf env pair.1 == module &&
        pair.2.type.getAppFn.isConstOf ``Registration)
      owned.toArray.map (fun pair => pair.2)
  let rows ← inputs.mapM fun info => do
    try row module info catch error =>
      return Json.mkObj [("module", toJson module), ("inputName", toJson info.name),
        ("error", toJson (← error.toMessageData.toString))]
  return Json.mkObj [("module", toJson module), ("registrations", Json.arr rows)]

def inputModules (env : Environment) : Std.HashMap Name (Array ConstantInfo) := Id.run do
  let mut modules : Std.HashMap Name (Array ConstantInfo) := {}
  for (name, info) in env.constants.toList do
    if info.type.getAppFn.isConstOf ``Registration then
      let owner := ownerOf env name
      modules := modules.insert owner ((modules[owner]?).getD #[] |>.push info)
  return modules

end K2SourceFactsGenerator

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let (all, module, output, modules) ← match args with
    | ["--all", output, moduleList] => do
      let names := ((← IO.FS.readFile moduleList).splitOn "\n").filterMap fun line =>
        let name := line.trimAscii.toString
        if name.isEmpty then none else some name.toName
      if names.isEmpty then throw <| IO.userError "empty module list"
      pure (true, Name.anonymous, output, names.toArray)
    | [moduleText, output] => do
      if moduleText == "--all" then
        throw <| IO.userError "--all OUTPUT_DIR MODULE_LIST_FILE required"
      let module := moduleText.toName
      pure (false, module, output, #[module])
    | _ => throw <| IO.userError "MODULE OUTPUT or --all OUTPUT_DIR MODULE_LIST_FILE required"
  let opts := ({} : Options).setBool `pp.all true |>.setBool `pp.notation false
    |>.setBool `pp.fullNames true |>.setBool `pp.universes true
    |>.setBool `pp.proofs true |>.set `maxHeartbeats (200000 : Nat)
  enableInitializersExecution
  let imports : Array Import := #[{
    module := `LeanInformationAuditInterface.Contract.NodeFactsCore, importAll := true }] ++
    modules.map fun module => { module, importAll := true }
  let env ← importModules imports
    opts (loadExts := true)
  let run := fun module inputs =>
    (K2SourceFactsGenerator.collect module inputs).run' |>.toIO'
      { fileName := "k2-source-generator", fileMap := default, options := opts }
      { env := env.setExporting false }
  if all then
    IO.FS.createDirAll output
    let modules := K2SourceFactsGenerator.inputModules env
    for module in modules.toArray.map (·.1) |>.qsort (fun a b => a.toString < b.toString) do
      let result ← run module modules[module]?
      IO.FS.writeFile (System.FilePath.mk output / (module.toString ++ ".json")) result.pretty
  else
    let result ← run module none
    IO.FS.writeFile output result.pretty
