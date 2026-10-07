import Lean
import LeanInformationAuditInterface.Contract.NodeFacts
import LeanInformationAudit.Contract.Literal
import LeanInformationAudit.ReadoutProvenance.View

open Lean Meta
open LeanInformationAudit.Contract

namespace K2FactsGenerator

open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr
open Lean.Parser.Term TSyntax.Compat

@[delab app] def literalApplication : Delab := do
  if (← getExpr).isConst then
    let name ← Lean.PrettyPrinter.Delaborator.delabConst
    return ← `(@$name)
  let fn ← withNaryFn delab
  let count := (← getExpr).getAppNumArgs
  let args ← (List.range count).toArray.mapM fun index => withNaryArg index delab
  let explicitFn ← if (← withNaryFn getExpr).isConst then pure fn else `(@$fn)
  return Syntax.mkApp explicitFn args

def literalBinder (id : Ident) (type : Term) (mode : BinderInfo) : DelabM (TSyntax ``Lean.Parser.Term.bracketedBinderF) :=
  match mode with
  | .default => `(bracketedBinderF| ($id:ident : $type))
  | .implicit => `(bracketedBinderF| {$id:ident : $type})
  | .strictImplicit => `(bracketedBinderF| ⦃$id:ident : $type⦄)
  | .instImplicit => `(bracketedBinderF| [$id:ident : $type])

def literalFunBinder (id : Ident) (type : Term) (mode : BinderInfo) : DelabM (TSyntax ``Lean.Parser.Term.funBinder) :=
  match mode with
  | .default => `(funBinder| ($id : $type))
  | .implicit => `(funBinder| {$id:ident : $type})
  | .strictImplicit => `(funBinder| ⦃$id:ident : $type⦄)
  | .instImplicit => `(funBinder| [$id:ident : $type])

@[delab lam] def literalLambda : Delab := do
  let mode := (← getExpr).binderInfo
  let type ← withBindingDomain delab
  withBindingBodyUnusedName fun id => do
    let binder ← literalFunBinder ⟨id⟩ type mode
    let body ← delab
    `(fun $binder:funBinder => $body)

@[delab forallE] def literalForall : Delab := do
  let mode := (← getExpr).binderInfo
  let type ← withBindingDomain delab
  withBindingBodyUnusedName fun id => do
    let binder ← literalBinder ⟨id⟩ type mode
    let body ← delab
    `(∀ $binder, $body)


initialize diagnosticStage : IO.Ref (String × Name × String × List String) ←
  IO.mkRef ("initial", .anonymous, "", [])
initialize diagnosticNodes : IO.Ref Nat ← IO.mkRef 0
initialize diagnosticCounts : IO.Ref (Array Nat) ← IO.mkRef (Array.replicate 16 0)
initialize printedTerms : IO.Ref (ExprStructMap String) ← IO.mkRef {}
initialize rawBindingKeys : IO.Ref (PHashMap UInt64 (Array (Expr × Expr × Expr))) ←
  IO.mkRef {}

/-- External migration measurements only. Hash collisions and alpha matches
 are separated by exact raw Expr equality, including checked types and levels. -/
def rawBindingKey (value type : Expr) (levels : List Level) : IO String := do
  let levelOperand := mkConst `K2RawCoordinateLevels levels
  let bucketHash := mixHash (mixHash value.hash type.hash) levelOperand.hash
  let bucket := ((← rawBindingKeys.get).find? bucketHash).getD #[]
  for index in [:bucket.size] do
    let (priorValue, priorType, priorLevels) := bucket[index]!
    if priorValue.equal value && priorType.equal type && priorLevels.equal levelOperand then
      return s!"raw:{bucketHash}:{index}"
  rawBindingKeys.modify (·.insert bucketHash (bucket.push (value, type, levelOperand)))
  return s!"raw:{bucketHash}:{bucket.size}"

partial def levelText : Level → String
  | .zero => ".zero"
  | .param name => ".param `" ++ name.toString
  | .succ level => ".succ (" ++ levelText level ++ ")"
  | .max a b => ".max (" ++ levelText a ++ ") (" ++ levelText b ++ ")"
  | .imax a b => ".imax (" ++ levelText a ++ ") (" ++ levelText b ++ ")"
  | .mvar _ => panic! "unexpected level metavariable"

partial def nameComponents : Name → List Json
  | .anonymous => []
  | .str namePrefix component => nameComponents namePrefix ++ [.str component]
  | .num namePrefix component => nameComponents namePrefix ++ [toJson component]

partial def levelTree : Level → Json
  | .zero => toJson #[Json.str "zero"]
  | .param name => toJson #[Json.str "param", toJson (nameComponents name)]
  | .succ nested => toJson #[Json.str "succ", levelTree nested]
  | .max left right => toJson #[Json.str "max", levelTree left, levelTree right]
  | .imax left right => toJson #[Json.str "imax", levelTree left, levelTree right]
  | .mvar _ => panic! "unexpected level metavariable"

def typeAt (declaration : Name) (part : String) (path : List String)
    (levels : List Level) : String :=
  let address := Json.mkObj [
    ("declaration", toJson (nameComponents declaration)), ("part", toJson part),
    ("path", toJson path), ("levels", toJson (levels.map levelTree))]
  "type_of% (@(compiled_node% " ++ (Json.str address.compress).compress ++ "))"

def headAt (declaration : Name) (part : String) (path : List String)
    (levels : List Level) : String :=
  let address := Json.mkObj [
    ("declaration", toJson (nameComponents declaration)), ("part", toJson part),
    ("path", toJson path), ("levels", toJson (levels.map levelTree))]
  "(@(compiled_head% " ++ (Json.str address.compress).compress ++ "))"

def ownerOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.header.modules[index.toNat]!.module
  | none => env.mainModule

initialize protectedModules : IO.Ref (Std.HashMap Name Bool) ← IO.mkRef {}
initialize currentOwner : IO.Ref Name ← IO.mkRef .anonymous

def setScope (env : Environment) (current : Name) : IO Unit := do
  currentOwner.set current
  if (← protectedModules.get).isEmpty then
    let modules := env.header.moduleNames
    let data := (modules.zip env.header.moduleData).foldl
      (fun table (name, value) => table.insert name value) ({} : Std.HashMap Name ModuleData)
    protectedModules.set <| LeanInformationAudit.RegistrationGates.compiledModuleClasses
      modules (data[·]?)

def protectedNode (env : Environment) (name : Name) : IO Bool := do
  let owner := ownerOf env name
  return owner == (← currentOwner.get) || ((← protectedModules.get)[owner]?).getD true

def text (e : Expr) : MetaM String := do
  diagnosticStage.modify fun (_, name, part, path) => ("pretty", name, part, path)
  if let some result := (← printedTerms.get)[ExprStructEq.mk e]? then return result
  let result := (← Lean.PrettyPrinter.ppExpr e).pretty 120
  printedTerms.modify (·.insert (ExprStructEq.mk e) result)
  return result

def coordText (owner declName : Name) (part : String) (path : List String)
    (levels : List Name) : String :=
  "{ owner := `" ++ owner.toString ++ ", declaration := `" ++ declName.toString ++
    ", part := ." ++ part ++ ", path := [" ++ String.intercalate ", " (path.map ("." ++ ·)) ++
    "], levels := [" ++ String.intercalate ", " (levels.map (fun n => ".param `" ++ n.toString)) ++ "] }"

structure Row where
  owner : Name
  declName : Name
  declarationComponents : List Json
  part : String
  path : List String
  type : String
  head : String
  hasHead : Bool
  role : String
  levels : List Name
  usedLevels : List Name
  headUsedLevels : List Name
  coordinateLevels : List String
  coordinateLevelTrees : List Json
  declarationLevels : List Name
  directReferences : List Name
  rigidInductive : Bool
  rawBindingKey : String
  headKey : String
  deriving ToJson, Inhabited

initialize diagnosticFailureRows : IO.Ref (Array Row) ← IO.mkRef #[]

inductive SubtreeTemplate where
  | node (row : Row) (children : Array (String × SubtreeTemplate)) (rowCount : Nat)
  deriving Inhabited

def SubtreeTemplate.rowCount : SubtreeTemplate → Nat
  | .node _ _ count => count

initialize subtreeTemplates : IO.Ref
    (ExprStructMap (Std.HashMap ((Nat × ExprStructEq) × List Name) SubtreeTemplate)) ←
  IO.mkRef {}
initialize diagnosticSubtreeReuse : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)

def subtreeReuseDelta (before after : Nat × Nat) : Json :=
  Json.mkObj [("templateHits", toJson (after.1 - before.1)),
    ("flattenedRows", toJson (after.2 - before.2))]

structure NodeSnapshot where
  hasHead : Bool
  role : String
  directReferences : List Name
  rigidInductive : Bool
  usedLevels : List Name
  headUsedLevels : List Name
  rawBindingKey : String
  headKey : String

initialize nodeSnapshots : IO.Ref
    (ExprStructMap (Std.HashMap (Nat × ExprStructEq) NodeSnapshot)) ← IO.mkRef {}
initialize declarationRows : IO.Ref (Std.HashMap (Name × String) (Array Row)) ← IO.mkRef {}

abbrev M := StateRefT (Array Row) MetaM

def inspectStep (declName : Name) (part : String) (path : List String)
    (stage : String) (action : MetaM α) : MetaM α := do
  diagnosticStage.set (stage, declName, part, path)
  let start ← IO.getNumHeartbeats
  try
    let result ← action
    let spent := (← IO.getNumHeartbeats) - start
    if spent > 1000000 then
      IO.eprintln s!"cost={spent} stage={stage} declaration={declName} path={path}"
    return result
  catch error =>
    IO.eprintln s!"failed stage={stage} declaration={declName} part={part} path={path}"
    throw error

def inferNodeType (e : Expr) : MetaM Expr := do
  match e with
  | .const constant levels =>
    let info ← getConstVal constant
    if info.levelParams.length == levels.length then
      instantiateTypeLevelParams info levels
    else
      throwIncorrectNumberOfLevels constant levels
  | .fvar id =>
    match (← getLCtx).find? id with
    | some entry => pure entry.type
    | none => id.throwUnknown
  | .lit literal => pure literal.type
  | .sort universeLevel => pure (mkSort (mkLevelSucc universeLevel))
  | _ => inferType e

def diagnosticDelta (before after : Array Nat) : Json :=
  let names := #["snapshotHits", "snapshotMisses", "inferConstant", "inferFvar",
    "inferLiteral", "inferSort", "inferApplication", "inferForall", "inferLambda",
    "inferLet", "inferProjection", "inferMetadata", "inferOther", "quickProof",
    "quickNonProof", "quickUnknown"]
  Json.mkObj ((names.zipIdx).toList.map fun (name, index) =>
    (name, toJson (after[index]! - before[index]!)))

def sourceLeaves (env : Environment) (info : ConstantInfo) : MetaM NameSet := do
  let mut pending : List Name := []
  let target := info.type.getAppArgs[1]!
  if let some original := env.find? target.getAppFn.constName! then
    pending := original.type.getUsedConstants.toList
  if let some value := info.value? then
    let fields := value.getAppArgs
    let selection ← IO.ofExcept <| Literal.optional "selection"
      (← IO.ofExcept <| Literal.referencedValue env.find? fields[fields.size - 4]!)
    if let some selection := selection then
      let ss ← IO.ofExcept <| Literal.fields env.find? ``SourceSelection selection 4
      let definition ← IO.ofExcept <| Literal.optional "definition"
        (← IO.ofExcept <| Literal.referencedValue env.find? ss[1]!)
      if let some definition := definition then
        let ds ← IO.ofExcept <| Literal.fields env.find? ``DefinitionSelection definition 3
        let sourceName ← IO.ofExcept <| Literal.name "definition.name" ds[1]!
        if let some source := env.find? sourceName then
          if let some value := source.value? then
            pending := value.getUsedConstants.toList ++ pending
  let mut found : NameSet := {}
  while let name :: rest := pending do
    pending := rest
    if found.contains name then continue
    found := found.insert name
    if let some declaration := env.find? name then
      pending := declaration.type.getUsedConstants.toList ++ pending
      if (ownerOf env name).getRoot == `D5 && !declaration.isTheorem then
        if let some value := declaration.value? then
          pending := value.getUsedConstants.toList ++ pending
  return found

partial def proofHeadName : Expr → Option Name
  | .const name _ => some name
  | .app function _ | .mdata _ function => proofHeadName function
  | _ => none

structure VisitContext where
  env : Environment
  declName : Name
  part : String
  levels : List Name
  owner : Name
  declarationComponents : List Json
  externalDeclaration : Bool
  actualLevels : List Level
  levelKey : ExprStructEq
  coordinateLevels : List String
  coordinateLevelTrees : List Json
  declarationLevels : List Name
  addressDeclaration : Json
  addressPart : Json
  addressLevels : Json

def VisitContext.quotedAddress (context : VisitContext) (path : List String) : String :=
  let address := Json.mkObj [
    ("declaration", context.addressDeclaration), ("part", context.addressPart),
    ("path", toJson path), ("levels", context.addressLevels)]
  (Json.str address.compress).compress

private def visitContext (env : Environment) (declName : Name) (part : String)
    (levels : List Name) (actualLevels : Option (List Level)) : IO VisitContext := do
  let actualLevels := actualLevels.getD (levels.map Level.param)
  let declarationComponents := nameComponents declName
  let coordinateLevelTrees := actualLevels.map levelTree
  return {
    env, declName, part, levels, owner := ownerOf env declName,
    declarationComponents, externalDeclaration := !(← protectedNode env declName),
    actualLevels, levelKey := ExprStructEq.mk (mkConst `K2RawCoordinateLevels actualLevels),
    coordinateLevels := actualLevels.map levelText, coordinateLevelTrees,
    declarationLevels := ((env.find? declName).map (·.levelParams)).getD [],
    addressDeclaration := toJson declarationComponents,
    addressPart := toJson part, addressLevels := toJson coordinateLevelTrees }

private def rebindRow (context : VisitContext) (path : List String) (row : Row) : Row :=
  let quotedAddress := if row.hasHead then context.quotedAddress path else ""
  { row with
    owner := context.owner, declName := context.declName,
    declarationComponents := context.declarationComponents, part := context.part, path,
    type := if row.hasHead then "type_of% (@(compiled_node% " ++ quotedAddress ++ "))" else "",
    head := if row.hasHead then "(@(compiled_head% " ++ quotedAddress ++ "))" else "",
    levels := context.levels, coordinateLevels := context.coordinateLevels,
    coordinateLevelTrees := context.coordinateLevelTrees,
    declarationLevels := context.declarationLevels }

partial def emitTemplate (context : VisitContext) (path : List String)
    (template : SubtreeTemplate) (depth : Nat) : M Unit := do
  if depth > 256 then throwError "generator depth: {context.declName}"
  let .node row children _ := template
  modify (·.push (rebindRow context path row))
  for (edge, child) in children do
    emitTemplate context (path ++ [edge]) child (depth + 1)

partial def visit (context : VisitContext) (path : List String)
    (xs : Array Expr) (e : Expr) (depth : Nat := 0) : M SubtreeTemplate := do
  let declName := context.declName
  let part := context.part
  let levels := context.levels
  if depth > 256 then throwError "generator depth: {declName}"
  let closed ← mkLambdaFVars xs e (usedOnly := false) (usedLetOnly := false)
    (etaReduce := false) (generalizeNondepLet := false)
  let checked := inspectStep declName part path
  let env := context.env
  let externalDeclaration := context.externalDeclaration
  let cacheKey := (xs.size * 2 + if externalDeclaration then 1 else 0,
    context.levelKey)
  let subtreeKey := (cacheKey, context.levels)
  if let some template := ((← subtreeTemplates.get)[ExprStructEq.mk closed]?).bind
      (·[subtreeKey]?) then
    emitTemplate context path template depth
    diagnosticNodes.modify (· + template.rowCount)
    diagnosticSubtreeReuse.modify fun (hits, rows) => (hits + 1, rows + template.rowCount)
    return template
  let cached := ((← nodeSnapshots.get)[ExprStructEq.mk closed]?).bind (·[cacheKey]?)
  let snapshot ← match cached with
    | some snapshot => pure snapshot
    | none => do
        let originalType ←
          checked s!"inferType:{e.getAppFn.constName?.getD .anonymous}:args={e.getAppNumArgs}" (inferNodeType e)
        let classification ← inspectStep declName part path "isProofQuick" (isPropQuick originalType)
        let proof := match classification with | .true => true | _ => false
        let raw := match classification with | .undef => true | _ => false
        let type := originalType
        let closedType ← mkForallFVars xs type (usedOnly := false) (usedLetOnly := false)
          (generalizeNondepLet := false)
        let typeNode := !raw && closedType.isSort
        let role := if raw then "raw" else if proof then "proof" else if typeNode then "type" else "data"
        let noOp ← match e with
          | .lit _ => pure true
          | .fvar id =>
            pure (((← getLCtx).get! id).value? (allowNondep := true)).isNone
          | _ => pure false
        let rigid := noOp || e.isSort || e.isLambda || e.isForall ||
          match env.find? (e.getAppFn.constName?.getD .anonymous) with
          | some (.inductInfo _) | some (.ctorInfo _) | some (.opaqueInfo _) | some (.axiomInfo _) => true
          | _ => false
        let projection := (env.getProjectionFnInfo? (e.getAppFn.constName?.getD .anonymous)).any
          (fun info => e.getAppNumArgs > info.numParams)
        let partialFunction := type.isForall
        let structuralType := #[`D5.S3.ConceptDynamics.InformationEscape,
          `LeanInformationAudit.Contract].any (·.isPrefixOf (type.getAppFn.constName?.getD .anonymous))
        let normalize := type.isSort || structuralType
        let normalized ← if proof || rigid || raw || externalDeclaration || partialFunction || !normalize then pure e
          else do
            let shape := match e with
              | .fvar _ => "fvar" | .bvar _ => "bvar" | .lit _ => "literal"
              | .letE .. => "let" | .lam .. => "lambda" | .forallE .. => "forall"
              | .sort .. => "sort" | .app .. => "application" | .const .. => "constant"
              | .proj .. => "projection" | .mdata .. => "metadata" | .mvar .. => "metavariable"
            let fvarValue ← match e with
              | .fvar id => pure (toString (((← getLCtx).get! id).value? (allowNondep := true)).isSome)
              | _ => pure "none"
            let letNondep := match e with | .letE _ _ _ _ nd => toString nd | _ => "none"
            checked s!"valueWhnf:{e.getAppFn.constName?.getD .anonymous}:args={e.getAppNumArgs}:forall={type.isForall}:projection={projection}:shape={shape}:fvarValue={fvarValue}:letNondep={letNondep}" (whnf e)
        let head ← mkLambdaFVars xs normalized (usedOnly := false) (usedLetOnly := false)
          (etaReduce := false) (generalizeNondepLet := false)
        let direct := if proof then (proofHeadName e).toList ++ type.getUsedConstants.toList else
          match e with | .const name _ => [name] | _ => []
        let direct := if normalized.equal e then direct else
          (direct ++ normalized.getUsedConstants.toList).eraseDups
        let direct := direct.flatMap fun name =>
          match env.find? name with
          | some (.inductInfo info) => name :: info.ctors
          | _ => [name]
        let hasHead := !normalized.equal e
        let snapshot : NodeSnapshot := {
          hasHead, role := role,
          directReferences := direct,
          usedLevels := (collectLevelParams
            (collectLevelParams (collectLevelParams {} closed) closedType) head).params.toList,
          headUsedLevels := (collectLevelParams
            (collectLevelParams {} closedType) head).params.toList,
          rigidInductive := match env.find? (normalized.getAppFn.constName?.getD .anonymous) with
            | some (.inductInfo _) => true
            | _ => false
          rawBindingKey := ← rawBindingKey closed closedType
            context.actualLevels
          headKey := ← rawBindingKey head closedType
            context.actualLevels }
        nodeSnapshots.modify fun cache =>
          let entries := (cache[ExprStructEq.mk closed]?).getD {}
          cache.insert (ExprStructEq.mk closed) (entries.insert cacheKey snapshot)
        pure snapshot
  let quotedAddress := if snapshot.hasHead then context.quotedAddress path else ""
  let row : Row := {
    owner := context.owner
    declName := declName
    declarationComponents := context.declarationComponents
    part := part
    path := path
    type := if snapshot.hasHead then
      "type_of% (@(compiled_node% " ++ quotedAddress ++ "))" else ""
    head := if snapshot.hasHead then
      "(@(compiled_head% " ++ quotedAddress ++ "))" else ""
    hasHead := snapshot.hasHead
    role := snapshot.role
    levels := levels
    usedLevels := levels.filter (snapshot.usedLevels.contains ·)
    headUsedLevels := levels.filter (snapshot.headUsedLevels.contains ·)
    coordinateLevels := context.coordinateLevels
    coordinateLevelTrees := context.coordinateLevelTrees
    declarationLevels := context.declarationLevels
    directReferences := snapshot.directReferences
    rigidInductive := snapshot.rigidInductive
    rawBindingKey := snapshot.rawBindingKey
    headKey := snapshot.headKey }
  modify (·.push row)
  diagnosticCounts.modify fun counts =>
    if cached.isSome then counts.modify 0 (· + 1)
    else
      let constructor := match e with
        | .const .. => 2 | .fvar .. => 3 | .lit .. => 4 | .sort .. => 5
        | .app .. => 6 | .forallE .. => 7 | .lam .. => 8 | .letE .. => 9
        | .proj .. => 10 | .mdata .. => 11 | _ => 12
      let classification := if snapshot.role == "proof" then 13 else
        if snapshot.role == "raw" then 15 else 14
      counts.modify 1 (· + 1) |>.modify constructor (· + 1) |>.modify classification (· + 1)
  diagnosticNodes.modify (· + 1)
  let children ← if snapshot.role == "proof" then pure #[] else do
    let child := fun edge expression =>
      visit context (path ++ [edge]) xs expression (depth + 1)
    match e with
    | .app f a =>
      let function ← child "function" f
      let argument ← child "argument" a
      pure #[ ("function", function), ("argument", argument) ]
    | .lam n t b bi | .forallE n t b bi =>
      let domain ← child "domain" t
      let body ← withLocalDecl n bi t fun x =>
        visit context (path ++ ["body"]) (xs.push x) (b.instantiate1 x) (depth + 1)
      pure #[ ("domain", domain), ("body", body) ]
    | .letE n t v b nd =>
      let type ← child "letType" t
      let value ← child "letValue" v
      let body ← withLetDecl n t v (nondep := nd) fun x =>
        visit context (path ++ ["letBody"]) (xs.push x) (b.instantiate1 x) (depth + 1)
      pure #[ ("letType", type), ("letValue", value), ("letBody", body) ]
    | .mdata _ b => pure #[ ("metadata", ← child "metadata" b) ]
    | .proj _ _ b => pure #[ ("projection", ← child "projection" b) ]
    | _ => pure #[]
  let count := children.foldl (fun count (_, child) => count + child.rowCount) 1
  let template := SubtreeTemplate.node row children count
  subtreeTemplates.modify fun cache =>
    let entries := (cache[ExprStructEq.mk closed]?).getD {}
    cache.insert (ExprStructEq.mk closed) (entries.insert subtreeKey template)
  return template

def visitRoot (declName : Name) (part : String) (levels : List Name)
    (path : List String) (xs : Array Expr) (e : Expr)
    (actualLevels : Option (List Level) := none) : M Unit := do
  let env ← getEnv
  let canonical := path.isEmpty && xs.isEmpty &&
    ((env.find? declName).any fun info => info.levelParams == levels) &&
    actualLevels.getD (levels.map Level.param) == levels.map Level.param &&
    (ownerOf env declName).getRoot != `Reg
  if canonical then
    if let some rows := (← declarationRows.get)[(declName, part)]? then
      modify (· ++ rows)
      diagnosticNodes.modify (· + rows.size)
      return
  let start := (← get).size
  let context ← visitContext env declName part levels actualLevels
  let _ ← visit context path xs e
  if canonical then
    let rows := (← get).extract start (← get).size
    declarationRows.modify (·.insert (declName, part) rows)

def collect (module : Name) (infos : List (Name × ConstantInfo)) : MetaM Json := do
  diagnosticFailureRows.set #[]
  printedTerms.set {}
  diagnosticNodes.set 0
  let env ← getEnv
  let inputs := infos.filter fun (_, i) =>
    #[``Registration, ``TemplateEnrollment].contains (i.type.getAppFn.constName?.getD .anonymous)
  let inputLeaves ← inputs.mapM fun (name, info) => do
    let leaves ← if info.type.getAppFn.isConstOf ``Registration then sourceLeaves env info
      else pure ({} : NameSet)
    return (name, leaves)
  let action : M (Array Row) := do
    for (name, info) in infos do
      if info.isTheorem then continue
      if let .defnInfo defn := info then
        if defn.safety != .safe then continue
        -- Input payloads contain their own certificate names and are added
        -- after generation; selected operands are printed separately below.
        if info.type.getAppFn.isConstOf ``Registration then
          let fields := defn.value.getAppArgs
          if fields.size ≥ 20 then
            let index := fields.size - 20 + 11
            let descriptor := fields[index]!
            for fieldIndex in [4, 5, 8] do
              let actualIndex := fields.size - 20 + fieldIndex
              let atField := List.replicate (fields.size - actualIndex - 1) "function" ++ ["argument"]
              visitRoot name "value" info.levelParams atField #[] fields[actualIndex]!
            let path := List.replicate (fields.size - index - 1) "function" ++ ["argument"]
            visitRoot name "value" info.levelParams path #[] descriptor
            let target := info.type.getAppArgs[1]!
            if let some original := env.find? target.getAppFn.constName! then
              let levels := target.getAppFn.constLevels!
              let body := Literal.instantiateRawLevels original.levelParams levels original.type
              visitRoot original.name "type" info.levelParams [] #[] body (some levels)
            let selection ← IO.ofExcept <| Literal.optional "selection"
              (← IO.ofExcept <| Literal.referencedValue env.find? fields[fields.size - 4]!)
            if let some selection := selection then
              let ss ← IO.ofExcept <| Literal.fields env.find? ``SourceSelection selection 4
              let definition ← IO.ofExcept <| Literal.optional "definition"
                (← IO.ofExcept <| Literal.referencedValue env.find? ss[1]!)
              if let some definition := definition then
                let ds ← IO.ofExcept <| Literal.fields env.find? ``DefinitionSelection definition 3
                let sourceName ← IO.ofExcept <| Literal.name "definition.name" ds[1]!
                if let some (.defnInfo source) := env.find? sourceName then
                  visitRoot sourceName "value" info.levelParams [] #[]
                    (Literal.instantiateRawLevels source.levelParams target.getAppFn.constLevels! source.value)
                    (some target.getAppFn.constLevels!)
        else if info.type.getAppFn.isConstOf ``TemplateEnrollment then
          let target := info.type.getAppArgs[1]!
          if let some original := env.find? target.getAppFn.constName! then
            let levels := target.getAppFn.constLevels!
            visitRoot original.name "type" info.levelParams [] #[]
              (Literal.instantiateRawLevels original.levelParams levels original.type) (some levels)
            if let some value := original.value? then
              visitRoot original.name "value" info.levelParams [] #[]
                (Literal.instantiateRawLevels original.levelParams levels value) (some levels)
          let fields ← IO.ofExcept <| Literal.fields env.find? ``TemplateEnrollment defn.value 4
          let constructors ← IO.ofExcept <| Literal.array "constructors"
            (← IO.ofExcept <| Literal.resolveReferences env.find? fields[2]!)
          for constructor in constructors do
            let fields ← IO.ofExcept <| Literal.fields env.find? ``TypeRef constructor 2
            let name ← IO.ofExcept <| Literal.name "constructor" fields[0]!
            let some original := env.find? name | throwError "missing constructor {name}"
            visitRoot name "type" original.levelParams [] #[] original.type
        else if inputs.isEmpty then
          unless #[``NodeFact, ``StatementExclusion].contains
              (info.type.getAppFn.constName?.getD .anonymous) do
            visitRoot name "type" info.levelParams [] #[] info.type
            visitRoot name "value" info.levelParams [] #[] defn.value
    let mut leaves : NameSet := {}
    let mut initialized := false
    for (name, info) in inputs do
      if info.type.getAppFn.isConstOf ``Registration then
        let current := ((inputLeaves.find? (·.1 == name)).map (·.2)).getD {}
        if initialized then
          leaves := leaves.toList.foldl (fun found name =>
            if current.contains name then found.insert name else found) {}
        else
          leaves := current
          initialized := true
    if inputs.any (fun (_, info) => info.type.getAppFn.isConstOf ``TemplateEnrollment) then
      leaves := {}
    let mut seen : NameSet := {}
    let initial ← get
    for row in initial do
      if let some info := env.find? row.declName then
        if row.coordinateLevels == (info.levelParams.map (fun n => levelText (.param n))) then
          seen := seen.insert row.declName
    let mut pending := initial.toList.flatMap (·.directReferences)
    while let name :: rest := pending do
      pending := rest
      if seen.contains name then continue
      seen := seen.insert name
      let some info := env.find? name | continue
      let start := (← get).size
      visitRoot name "type" info.levelParams [] #[] info.type
      if let .inductInfo inductiveInfo := info then
        pending := inductiveInfo.ctors ++ pending
      if !leaves.contains name && (← protectedNode env name) then
        if let .defnInfo defn := info then
          if defn.safety == .safe then
            let classification ← inspectStep name "type" [] "declarationProofBoundaryQuick" (isPropQuick info.type)
            let proof := match classification with | .true => true | _ => false
            unless proof do visitRoot name "value" info.levelParams [] #[] defn.value
      let added := (← get).extract start (← get).size
      pending := added.toList.flatMap (·.directReferences) ++ pending
    get
  let capturedAction : M (Array Row) :=
    tryCatchRuntimeEx action fun error => do
      diagnosticFailureRows.set (← get)
      throw error
  let (nodes, _) ← capturedAction.run #[]
  let rows ← inputs.toArray.mapM fun (name, info) => do
    let some value := info.value? | throwError "missing input {name}"
    let root := fun (declName : Name) (part : String) (path : List String) => Json.mkObj [
      ("owner", toJson (ownerOf env declName)), ("declName", toJson declName),
      ("part", toJson part), ("path", toJson path), ("levels", toJson info.levelParams),
      ("coordinateLevels", toJson ((if declName == name then info.levelParams.map Level.param else
        info.type.getAppArgs[1]!.getAppFn.constLevels!).map levelText))]
    let mut roots : Array Json := #[]
    if info.type.getAppFn.isConstOf ``Registration then
      let fields := value.getAppArgs
      let target := info.type.getAppArgs[1]!
      roots := #[root target.getAppFn.constName! "type" [],
        root name "value" (List.replicate 16 "function" ++ ["argument"]),
        root name "value" (List.replicate 20 "function" ++ ["argument"]),
        root name "value" (List.replicate 19 "function" ++ ["argument"])]
      let descriptor ← IO.ofExcept <| Literal.optional "descriptor"
        (← IO.ofExcept <| Literal.referencedValue env.find? fields[fields.size - 9]!)
      if descriptor.isSome then
        roots := roots.push (root name "value" (List.replicate 13 "function" ++ ["argument", "argument"]))
      let selection ← IO.ofExcept <| Literal.optional "selection"
        (← IO.ofExcept <| Literal.referencedValue env.find? fields[fields.size - 4]!)
      if let some selection := selection then
        let ss ← IO.ofExcept <| Literal.fields env.find? ``SourceSelection selection 4
        let definition ← IO.ofExcept <| Literal.optional "definition"
          (← IO.ofExcept <| Literal.referencedValue env.find? ss[1]!)
        if let some definition := definition then
          let ds ← IO.ofExcept <| Literal.fields env.find? ``DefinitionSelection definition 3
          let sourceName ← IO.ofExcept <| Literal.name "definition.name" ds[1]!
          roots := roots.push (root sourceName "value" [])
    else if info.type.getAppFn.isConstOf ``TemplateEnrollment then
      let target := info.type.getAppArgs[1]!
      let name := target.getAppFn.constName!
      let some original := env.find? name | throwError "missing template {name}"
      let templateRoot := fun (declaration : Name) (part : String) (levels : List Name) => Json.mkObj [
        ("owner", toJson (ownerOf env declaration)), ("declName", toJson declaration),
        ("part", toJson part), ("path", toJson ([] : List String)), ("levels", toJson levels),
        ("coordinateLevels", toJson (levels.map (fun n => levelText (.param n))))]
      roots := #[templateRoot name "type" original.levelParams,
        templateRoot name "value" original.levelParams]
      let fields ← IO.ofExcept <| Literal.fields env.find? ``TemplateEnrollment value 4
      let constructors ← IO.ofExcept <| Literal.array "constructors"
        (← IO.ofExcept <| Literal.resolveReferences env.find? fields[2]!)
      for constructor in constructors do
        let fields ← IO.ofExcept <| Literal.fields env.find? ``TypeRef constructor 2
        let name ← IO.ofExcept <| Literal.name "constructor" fields[0]!
        let some original := env.find? name | throwError "missing constructor {name}"
        roots := roots.push (templateRoot name "type" original.levelParams)
    let leaves := ((inputLeaves.find? (·.1 == name)).map (·.2.toList)).getD []
    return Json.mkObj [
      ("roots", Json.arr roots),
      ("sourceLeaves", toJson leaves),
      ("name", toJson name), ("levels", toJson info.levelParams),
      ("type", toJson (← text info.type.getAppFn)),
      ("target", toJson (info.type.getAppArgs[1]!.getAppFn.constName?.getD .anonymous))]
  return Json.mkObj [("module", toJson module), ("inputs", Json.arr rows), ("nodes", toJson nodes)]

end K2FactsGenerator
