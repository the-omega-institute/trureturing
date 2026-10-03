import LeanInformationAudit.Registry
import LeanInformationAudit.Contract.Literal
import LeanInformationAuditContract.Registration
import LeanInformationAuditContract.Catalog

namespace LeanInformationAudit.Contract.Decoder
open Lean Meta

structure CompanionInput where
  input : RegistrationInput
  generated : Bool
  bridge : Expr
  target : Expr
  variation : Option Expr
  positive : Option Expr

def liftLiteral {α : Type} (value : Except String α) : MetaM α :=
  match value with
  | .ok value => pure value
  | .error error => throwError "{error}"

def fields (name : Name) (e : Expr) (count : Nat) : MetaM (Array Expr) := do
  let .ctorInfo ctor ← getConstInfo (name.str "mk")
    | throwError "contract.literal:unknown_structure:{name}"
  let args ← liftLiteral <| Literal.constructor (name.str "mk")
    (ctor.numParams + count) name.toString e
  return args.extract ctor.numParams args.size

private def constantHead (e : Expr) : Option Name :=
  match e with
  | .mdata _ body => constantHead body
  | .app function _ => constantHead function
  | .const name _ => some name
  | _ => none

private def constantName (role : String) (value : Expr) : MetaM Name := do
  unless Literal.closed value do
    throwError "incomplete_closure:contract.reference_open:{role}"
  let some name := constantHead value
    | throwError "unclassified_form:contract.reference_head:{role}"
  unless ((← getEnv).find? name).isSome do
    throwError "unclassified_form:contract.reference_unknown:{role}:{name}"
  return name

/-- Recover payload identity from its compiled constant head without reduction. -/
def reference (role : String) (e : Expr) : MetaM (Name × Expr) := do
  unless Literal.closed e do
    throwError "incomplete_closure:contract.reference_open:{role}"
  let fs ← fields ``Contract.Ref e 1
  let value := fs[0]!
  return (← constantName role value, value)

private def optional (e : Expr) : MetaM (Option Expr) :=
  liftLiteral <| Literal.optional "option" e

private def optionalRef (role : String) (e : Expr) : MetaM (Option (Name × Expr)) := do
  (← optional e).mapM (reference role)

private def arrayValues (e : Expr) : MetaM (Array Expr) :=
  liftLiteral <| Literal.array "array" e

private def sourceSelection (e : Expr) : MetaM LeanInformationAudit.SourceSelection := do
  let s ← liftLiteral <| Literal.sourceSelection e
  return { owner := s.owner
           definition := s.definition.map fun d => { owner := d.owner, name := d.name, path := d.path }
           coordinates := s.coordinates
           readouts := s.readouts.map fun r => {
             path := r.path, stateBinder := r.stateBinder, functionOperand := r.functionOperand
             stateOperand := r.stateOperand, booleanPredicate := r.booleanPredicate } }

private def continuation (e : Expr) : MetaM (Bool × Option Expr) := do
  let e := e.consumeMData
  if e.isAppOf ``Contract.Continuation.absent then return (false, none)
  if e.isAppOf ``Contract.Continuation.unknown then return (true, none)
  if e.isAppOf ``Contract.Continuation.evidence then
    return (false, some (← reference "continuation" e.getAppArgs.back!).2)
  throwError "unclassified_form:contract.continuation"

def checkTarget (name : Name) (value : Expr) : MetaM ConstantInfo := do
  let value := value.consumeMData
  unless value.isConst && value.constName! == name do
    throwError "unclassified_form:contract.target_identity:{name}"
  let info ← getConstInfo name
  unless info.isTheorem && Literal.closed info.type do
    throwError "unclassified_form:contract.target_theorem:{name}"
  unless value.constLevels!.length == info.levelParams.length do
    throwError "unclassified_form:contract.target_statement:{name}"
  return info

def rigidLevels (info : DefinitionVal) (value : Expr) : MetaM Unit := do
  let value := value.consumeMData
  unless value.isConst && value.constLevels! == info.levelParams.map Level.param do
    throwError "contract.discovery:rigid_universes:{info.name}"

def registration (owner : Name) (info : DefinitionVal) (source : String)
    : MetaM CompanionInput := do
  let all ← fields ``Contract.Registration info.value 17
  let typeArgs := info.type.getAppArgs
  unless typeArgs.size == 10 do throwError "contract.registration:target_arity"
  let theoremName ← constantName "target" typeArgs[1]!
  discard <| checkTarget theoremName typeArgs[1]!
  rigidLevels info typeArgs[1]!
  let fs := all.extract 4 all.size
  let (arenaName, _) ← reference "arena" fs[0]!
  let (objectArenaName, _) ← reference "object_arena" fs[1]!
  unless !arenaName.isAnonymous && !objectArenaName.isAnonymous do
    throwError "contract.registration:arena_identity"
  let catalog ← liftLiteral <| Literal.name "catalog" fs[2]!
  let localNames ← liftLiteral <| Literal.bool "local_names" fs[3]!
  let implementation := fs[4]!.consumeMData
  let head := implementation.getAppFn.constName?.getD .anonymous
  unless #[``Contract.Implementation.legacy, ``Contract.Implementation.forward,
      ``Contract.Implementation.witness, ``Contract.Implementation.source].contains head do
    throwError "contract.literal:implementation:nonliteral:{head}"
  let implementationArgs := implementation.getAppArgs
  let sourceBound := head == ``Contract.Implementation.source
  let witness := head == ``Contract.Implementation.witness
  let expectedArity := if sourceBound then 3 else if witness then 6 else 5
  unless implementationArgs.size == expectedArity do
    throwError "contract.registration:implementation_arity"
  let bridgeField := if witness then implementationArgs[implementationArgs.size - 2]!
    else implementationArgs.back!
  let (suppliedName, bridge) ← reference "realization" bridgeField
  let occurrence := !sourceBound && !localNames
  let family ← optionalRef "family_record" fs[11]!
  let unitName ← liftLiteral <| Literal.name "unit_name" all[0]!
  let realizationName ← liftLiteral <| Literal.name "realization_name" all[1]!
  let realizationSource ← (← optional all[2]!).mapM fun e =>
    liftLiteral <| Literal.name "realization_source" e
  if realizationSource.any (· != suppliedName) then
    throwError "contract.registration:realization_source_identity"
  let generated ← liftLiteral <| Literal.bool "generated" all[3]!
  unless !unitName.isAnonymous && !realizationName.isAnonymous do
    throwError "contract.registration:companion_identity"
  if sourceBound && (generated || realizationName != suppliedName) then
    throwError "contract.registration:source_bridge_identity"
  let descriptor ← optional fs[5]!
  let primitives := if sourceBound then none else some
    implementationArgs[implementationArgs.size - (if witness then 3 else 2)]!
  let positive := if witness then some implementationArgs.back! else none
  let variation ← optionalRef "variation" fs[6]!
  let sensitivity ← optionalRef "sensitivity" fs[7]!
  let origin ← optional fs[8]!
  let selection ← (← optional fs[9]!).mapM sourceSelection
  let (openContinuation, residual) ← continuation fs[10]!
  let options ← liftLiteral <| Literal.options fs[12]!
  let entry : InformationRegistryEntry := {
    theoremName, unitName, arenaName, realizationName
    catalogId := if occurrence then catalog else .anonymous
    registrationModuleName := owner
    objectArenaName := if sourceBound || occurrence then objectArenaName else .anonymous
    localRegistrationNames := localNames
    sourceBound, resolvedArenaName := if sourceBound then arenaName else .anonymous
    variationWitness := variation.map Prod.fst |>.getD .anonymous
    sensitivityWitness := sensitivity.map Prod.fst |>.getD .anonymous }
  let declaration := if descriptor.isSome || selection.isSome || origin.isSome ||
      openContinuation || residual.isSome then some {
      theoremName, arena := if occurrence then objectArenaName else arenaName
      descriptor, sourceRecord := if sourceBound then some suppliedName else family.map Prod.fst
      escapeInput := {
        sourceSelection := selection
        finiteBridge := if family.isSome then some suppliedName else none
        fromObject := origin, continuation := residual, openContinuation }
      : TemplateBinding.ResolvedDeclaration } else none
  return {
    input := {
      entry, sourceText := source, options, suppliedPrimitives := primitives, declaration
      realizationSource }
    generated, bridge, target := typeArgs[1]!, variation := variation.map Prod.snd, positive }

def expectedRow (e : Expr) : MetaM SnapshotOccurrence := do
  let fs ← fields ``Contract.ExpectedOccurrence e 6
  let theoremName ← liftLiteral <| Literal.name "name" fs[2]!
  let info ← checkTarget theoremName fs[1]!
  let objectArenaName ← liftLiteral <| Literal.name "name" fs[3]!
  discard <| getConstInfo objectArenaName
  let statementIdentity ← (← optional fs[4]!).mapM fun e =>
    liftLiteral <| Literal.string "statement_identity" e
  let registrationModuleName ← liftLiteral <| Literal.name "name" fs[5]!
  return {
    theoremName, objectArenaName
    statementIdentity := statementIdentity.getD ""
    capturedStatement := if statementIdentity.isSome then none else some info.type
    registrationModuleName }

def rootCatalog (e : Expr) : MetaM RootCatalogContract := do
  let outer ← fields ``Contract.RootCatalog e 1
  let fs ← fields ``Contract.RootCatalogData outer[0]! 5
  let rootId ← liftLiteral <| Literal.name "name" fs[0]!
  let expected ← (← arrayValues fs[1]!).mapM expectedRow
  let source ← (← arrayValues fs[2]!).mapM expectedRow
  let baseline ← (← arrayValues fs[3]!).mapM expectedRow
  let companionPrefix ← (← optional fs[4]!).mapM fun e =>
    liftLiteral <| Literal.name "companion_prefix" e
  return { rootId, expected, source, baseline, companionPrefix }

def enrollment (owner : Name) (info : DefinitionVal) (source : String) :
    MetaM TemplateEnrollmentInput := do
  let fs ← fields ``Contract.TemplateEnrollment info.value 4
  let name ← liftLiteral <| Literal.name "name" fs[0]!
  let args := info.type.getAppArgs
  unless args.size ≥ 2 && args[1]!.getAppFn.constName? == some name do
    throwError "unclassified_form:contract.template_identity:{name}"
  rigidLevels info args[1]!
  discard <| getConstInfo name
  let version ← liftLiteral <| Literal.nat "nat" fs[1]!
  let constructors ← (← arrayValues fs[2]!).mapM fun e => do
    let fs ← fields ``Contract.TypeRef e 2
    let name ← liftLiteral <| Literal.name "name" fs[0]!
    unless fs[1]!.getAppFn.constName? == some name do
      throwError "unclassified_form:contract.constructor_identity:{name}"
    discard <| getConstInfo name
    return name
  let options ← liftLiteral <| Literal.options fs[3]!
  return { owner, name, version, constructors, sourceText := source, options }

def readSeal (e : Expr) : MetaM SealInput := do
  let fs ← fields ``Contract.Seal e 2
  return { rootId := ← liftLiteral <| Literal.name "seal.root" fs[0]!
           options := ← liftLiteral <| Literal.options fs[1]! }

end LeanInformationAudit.Contract.Decoder
