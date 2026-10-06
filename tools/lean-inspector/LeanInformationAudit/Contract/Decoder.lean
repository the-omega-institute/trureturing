import LeanInformationAudit.Registry
import LeanInformationAudit.Contract.Literal
import LeanInformationAudit.Contract.CompiledExpressions
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAudit.Contract.Decoder
open Lean Meta
open D5.S3.ConceptDynamics.InformationEscape

structure CompanionInput where
  input : RegistrationInput
  generated : Bool
  bridge : Expr
  target : Expr
  variation : Option Expr
  positive : Option Expr
  unit : Option Expr

def liftLiteral {α : Type} (value : Except String α) : MetaM α :=
  match value with
  | .ok value => pure value
  | .error error => throwError "{error}"

/-- Follow at most 4096 compiled definition references. Applications,
projections and recursors require computation and have no decoding route. -/
def referencedValue (find : Name → Option ConstantInfo) (value : Expr)
    (seen : NameSet := {}) : IO Expr := do
  IO.ofExcept <| Literal.referencedValue find value seen

def fields (find : Name → Option ConstantInfo) (name : Name) (e : Expr)
    (count : Nat) : IO (Array Expr) := do
  IO.ofExcept <| Literal.fields find name e count

def compiledMetadata (find : Name → Option ConstantInfo) (value : Expr)
    (decode : Expr → Except String α) : Except String α := do
  decode (← Literal.resolveReferences find value)

def metadata (find : Name → Option ConstantInfo) (value : Expr) (decode : Expr → Except String α) : IO α := do
  IO.ofExcept <| compiledMetadata find value decode

private def constantName (find : Name → Option ConstantInfo) (role : String) (value : Expr) : IO Name := do
  IO.ofExcept <| Literal.constantName find role value

/-- Recover payload identity from its compiled constant head without reduction. -/
def reference (find : Name → Option ConstantInfo) (role : String) (e : Expr) : IO (Name × Expr) := do
  IO.ofExcept <| Literal.reference find role e

private def optional (find : Name → Option ConstantInfo) (e : Expr) : IO (Option Expr) := do
  IO.ofExcept <| Literal.optional "option" (← referencedValue find e)

private def optionalRef (find : Name → Option ConstantInfo) (role : String) (e : Expr) : IO (Option (Name × Expr)) := do
  (← optional find e).mapM (reference find role)

/-- Read an indexed obligation's constructor and the original submitted name.
The proof field was checked when its containing Reg declaration compiled. -/
private def obligation (find : Name → Option ConstantInfo) (e : Expr) :
    IO (CompiledObligationState × Option (Name × Expr)) := do
  let e := (← referencedValue find e).consumeMData
  if e.isAppOf ``Contract.Obligation.evidence then
    let args := e.getAppArgs
    return (.evidence, some (← reference find "obligation" args[args.size - 2]!))
  if e.isAppOf ``Contract.Obligation.unsupported then
    let name ← metadata find e.getAppArgs.back! (Literal.name "obligation.unsupported")
    return (.unsupported, some (name, mkConst name))
  if e.isAppOf ``Contract.Obligation.unknown then return (.unknown, none)
  if e.isAppOf ``Contract.Obligation.absent then return (.absent, none)
  throw <| IO.userError "contract.literal:obligation"

private def obligationState (find : Name → Option ConstantInfo) (e : Expr) :
    IO CompiledObligationState := do
  let head := (← referencedValue find e).consumeMData.getAppFn.constName?
  if head == some ``Contract.Obligation.evidence || head == some ``Contract.ExactMatch.evidence then
    return .evidence
  if head == some ``Contract.Obligation.unsupported || head == some ``Contract.ExactMatch.unsupported then
    return .unsupported
  if head == some ``Contract.Obligation.unknown || head == some ``Contract.ExactMatch.unknown then
    return .unknown
  if head == some ``Contract.Obligation.absent || head == some ``Contract.ExactMatch.absent then
    return .absent
  throw <| IO.userError "contract.literal:obligation"

private def arenaReference (find : Name → Option ConstantInfo) (role : String) (e : Expr) : IO (Name × Expr) := do
  let head := (← referencedValue find e).consumeMData.getAppFn.constName?.getD .anonymous
  unless #[``Contract.ArenaRef.law, ``Contract.ArenaRef.finite, ``Contract.ArenaRef.object,
      ``Contract.ArenaRef.witness, ``Contract.ArenaRef.source].contains head do
    throw <| IO.userError s!"contract.literal:arena:{role}"
  reference find role e.getAppArgs.back!

private def arrayValues (find : Name → Option ConstantInfo) (e : Expr) : IO (Array Expr) := do
  IO.ofExcept <| Literal.array "array" (← referencedValue find e)

private def sourceSelection (find : Name → Option ConstantInfo) (e : Expr) : IO LeanInformationAudit.SourceSelection := do
  let s ← metadata find e Literal.sourceSelection
  return { owner := s.owner
           definition := s.definition.map fun d => { owner := d.owner, name := d.name, path := d.path }
           coordinates := s.coordinates
           readouts := s.readouts.map fun r => {
             path := r.path, stateBinder := r.stateBinder, functionOperand := r.functionOperand
             stateOperand := r.stateOperand, booleanPredicate := r.booleanPredicate } }

private def continuation (find : Name → Option ConstantInfo) (e : Expr) : IO (Bool × Option Expr) := do
  let e := (← referencedValue find e).consumeMData
  if e.isAppOf ``Contract.Continuation.absent then return (false, none)
  if e.isAppOf ``Contract.Continuation.unknown then return (true, none)
  if e.isAppOf ``Contract.Continuation.evidence then
    return (false, some (← reference find "continuation" e.getAppArgs.back!).2)
  throw <| IO.userError "unclassified_form:contract.continuation"

def checkTarget (find : Name → Option ConstantInfo) (name : Name)
    (value : Expr) : Except String ConstantInfo := do
  let value := value.consumeMData
  unless value.isConst && value.constName! == name do
    throw s!"unclassified_form:contract.target_identity:{name}"
  let some info := find name
    | throw s!"contract.cannot_decode:{name}:missing_constant"
  unless info.isTheorem && Literal.closed info.type do
    throw s!"unclassified_form:contract.target_theorem:{name}"
  unless value.constLevels!.length == info.levelParams.length do
    throw s!"unclassified_form:contract.target_statement:{name}"
  return info

def rigidLevels (info : DefinitionVal) (value : Expr) : Except String Unit := do
  let value := value.consumeMData
  unless value.isConst && value.constLevels! == info.levelParams.map Level.param do
    throw s!"contract.discovery:rigid_universes:{info.name}"

def registration (context : CompiledExpressions.Context) (axioms : Array Name)
    (owner : Name) (info : DefinitionVal) (source : String)
    : IO CompanionInput := do
  let find := context.find
  let all ← fields find ``Contract.Registration info.value 20
  let trusted := axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·)
  let typeArgs := info.type.getAppArgs
  unless typeArgs.size == 5 do throw <| IO.userError "contract.registration:target_arity"
  let theoremName ← constantName find "target" typeArgs[1]!
  discard <| IO.ofExcept <| checkTarget find theoremName typeArgs[1]!
  IO.ofExcept <| rigidLevels info typeArgs[1]!
  let fs := all.extract 4 all.size
  let (arenaName, _) ← arenaReference find "arena" fs[0]!
  let (objectArenaName, _) ← arenaReference find "object_arena" fs[1]!
  unless !arenaName.isAnonymous && !objectArenaName.isAnonymous do
    throw <| IO.userError "contract.registration:arena_identity"
  let catalog ← metadata find fs[2]! (Literal.name "catalog")
  let localNames ← metadata find fs[3]! (Literal.bool "local_names")
  let implementation := (← referencedValue find fs[4]!).consumeMData
  let head := implementation.getAppFn.constName?.getD .anonymous
  unless #[``Contract.Implementation.legacy, ``Contract.Implementation.forward,
      ``Contract.Implementation.witness, ``Contract.Implementation.source].contains head do
    throw <| IO.userError s!"contract.literal:implementation:nonliteral:{head}"
  let implementationArgs := implementation.getAppArgs
  let sourceBound := head == ``Contract.Implementation.source
  let witness := head == ``Contract.Implementation.witness
  let expectedArity := if sourceBound then 3 else if witness then 10 else 7
  unless implementationArgs.size == expectedArity do
    throw <| IO.userError "contract.registration:implementation_arity"
  let bridgeField := implementationArgs[if sourceBound then 2 else 4]!
  let (suppliedName, bridge) ← reference find "realization" bridgeField
  let occurrence := !sourceBound && !localNames
  let family ← (← optional find fs[14]!).mapM fun e =>
    reference find "family_record" e.getAppArgs.back!
  let unitName ← metadata find all[0]! (Literal.name "unit_name")
  let realizationName ← metadata find all[1]! (Literal.name "realization_name")
  let realizationSource ← (← optional find all[2]!).mapM fun e =>
    metadata find e (Literal.name "realization_source")
  if realizationSource.any (· != suppliedName) then
    throw <| IO.userError "contract.registration:realization_source_identity"
  let generated ← metadata find all[3]! (Literal.bool "generated")
  unless !unitName.isAnonymous && !realizationName.isAnonymous do
    throw <| IO.userError "contract.registration:companion_identity"
  if sourceBound && (generated || realizationName != suppliedName) then
    throw <| IO.userError "contract.registration:source_bridge_identity"
  let descriptor ← optional find fs[7]!
  let primitives := if sourceBound then none else some
    implementationArgs[3]!
  let positive := if witness then some implementationArgs[5]! else none
  let (unit, unitCorrespondence) ← if sourceBound then pure (none, true) else do
    let bound ← fields find ``Contract.BoundTheoremUnit implementationArgs.back! 3
    let value ← fields find ``Contract.Ref bound[0]! 1
    pure (some value[0]!, (← obligationState find bound[1]!) == .evidence &&
      (← obligationState find bound[2]!) == .evidence &&
      (← obligationState find implementationArgs[if witness then 8 else 5]!) == .evidence)
  let (variationState, variation, witnessPositive, witnessNegative) ← if witness then do
    let parts ← fields find ``Contract.Implementation.WitnessVariationEvidence fs[8]! 2
    let (positiveState, positiveInput) ← obligation find parts[0]!
    let (negativeState, negativeInput) ← obligation find parts[1]!
    pure (if positiveState == .evidence then negativeState else positiveState,
      positiveInput.or negativeInput, positiveState, negativeState)
  else do
    let (state, value) ← obligation find fs[8]!
    pure (state, value, .evidence, .evidence)
  let (sensitivityState, sensitivity) ← obligation find fs[9]!
  let partialEvidence ← (← optional find fs[10]!).mapM fun e => do
    if sourceBound then throw <| IO.userError "contract.sensitivity:finite_slots_required"
    let values ← fields find ``Contract.Implementation.PartialSlotEvidence e 2
    let computation : CompiledExpressions.M (Array Bool × Array Bool) := do
      let arena := implementationArgs[1]!
      let arenaType ← CompiledExpressions.head (← CompiledExpressions.typeShape arena)
      let law := if witness then
        mkApp (mkConst (RegistrationElaboration.witnessArenaName.str "toPrimitiveLawArena")
          arenaType.getAppFn.constLevels!) arena else arena
      let signature := Expr.proj ``PrimitiveLawArena 1 law
      let readouts ← CompiledExpressions.partialSlotStates values[0]!
        (.proj ``PrimitiveSignature 1 signature)
      let anchors ← CompiledExpressions.partialSlotStates values[1]!
        (.proj ``PrimitiveSignature 8 signature)
      return (readouts, anchors)
    let ((readouts, anchors), _) ← CompiledExpressions.run context computation
    return (readouts, anchors)
  let origin ← optional find fs[11]!
  let selection ← (← optional find fs[12]!).mapM (sourceSelection find)
  let (openContinuation, residual) ← continuation find fs[13]!
  let options ← metadata find fs[15]! Literal.options
  let correspondenceFields ← fields find ``Contract.Implementation.Correspondence fs[5]! 2
  let stage ← obligationState find correspondenceFields[0]!
  let objectStage ← obligationState find correspondenceFields[1]!
  let correspondence := if stage == .evidence && objectStage == .evidence
    then .evidence else .unsupported
  let witnessActual ← if witness then obligationState find implementationArgs[6]! else pure .evidence
  let witnessStatement ← if witness then obligationState find implementationArgs[7]! else pure .evidence
  let entry : InformationRegistryEntry := {
    theoremName, unitName, arenaName, realizationName
    catalogId := if occurrence then catalog else .anonymous
    registrationModuleName := owner
    objectArenaName := if sourceBound || occurrence then objectArenaName else .anonymous
    localRegistrationNames := localNames
    sourceBound, resolvedArenaName := if sourceBound then arenaName else .anonymous
    variationWitness := variation.map Prod.fst |>.getD .anonymous
    sensitivityWitness := sensitivity.map Prod.fst |>.getD .anonymous
    compiledMathematics := some {
      witness,
      correspondence := if unitCorrespondence && trusted then correspondence else .unsupported,
      bundleNonempty := ← obligationState find fs[6]!,
      variation := variationState, sensitivity := sensitivityState,
      witnessPositive, witnessNegative, witnessActual, witnessStatement,
      partialReadouts := partialEvidence.map Prod.fst, partialAnchors := partialEvidence.map Prod.snd } }
  let declaration := if descriptor.isSome || selection.isSome || origin.isSome ||
      openContinuation || residual.isSome then some {
      theoremName, arena := if occurrence then objectArenaName else arenaName
      descriptor,
      sourceRecord := if sourceBound then some suppliedName else family.map Prod.fst
      escapeInput := {
        sourceSelection := selection
        finiteBridge := if family.isSome then some suppliedName else none
        fromObject := origin, continuation := residual, openContinuation }
      : TemplateBinding.ResolvedDeclaration } else none
  return {
    input := {
      entry, sourceText := source, options, suppliedPrimitives := primitives, declaration
      realizationSource }
    generated, bridge, target := typeArgs[1]!, variation := variation.map Prod.snd, positive, unit }

private def compiledConstant (find : Name → Option ConstantInfo)
    (name : Name) : Except String ConstantInfo := do
  let some info := find name
    | throw s!"contract.cannot_decode:{name}:missing_constant"
  return info

private def compiledOptional (find : Name → Option ConstantInfo)
    (e : Expr) : Except String (Option Expr) := do
  Literal.optional "option" (← Literal.referencedValue find e)

private def compiledArray (find : Name → Option ConstantInfo)
    (e : Expr) : Except String (Array Expr) := do
  Literal.array "array" (← Literal.referencedValue find e)

/-- The original theorem type and identity come from compiled constant data. -/
def expectedRow (find : Name → Option ConstantInfo) (e : Expr) :
    Except String SnapshotOccurrence := do
  let fs ← Literal.fields find ``Contract.ExpectedOccurrence e 6
  let theoremName ← compiledMetadata find fs[2]! (Literal.name "name")
  let info ← checkTarget find theoremName fs[1]!
  let objectArenaName ← compiledMetadata find fs[3]! (Literal.name "name")
  discard <| compiledConstant find objectArenaName
  let statementIdentity ← (← compiledOptional find fs[4]!).mapM fun e =>
    compiledMetadata find e (Literal.string "statement_identity")
  let registrationModuleName ← compiledMetadata find fs[5]! (Literal.name "name")
  return {
    theoremName, objectArenaName
    statementIdentity := statementIdentity.getD ""
    capturedStatement := if statementIdentity.isSome then none else some info.type
    registrationModuleName }

def rootCatalog (find : Name → Option ConstantInfo) (e : Expr) :
    Except String RootCatalogContract := do
  let outer ← Literal.fields find ``Contract.RootCatalog e 1
  let fs ← Literal.fields find ``Contract.RootCatalogData outer[0]! 5
  let rootId ← compiledMetadata find fs[0]! (Literal.name "name")
  let expected ← (← compiledArray find fs[1]!).mapM (expectedRow find)
  let source ← (← compiledArray find fs[2]!).mapM (expectedRow find)
  let baseline ← (← compiledArray find fs[3]!).mapM (expectedRow find)
  let companionPrefix ← (← compiledOptional find fs[4]!).mapM fun e =>
    compiledMetadata find e (Literal.name "companion_prefix")
  return { rootId, expected, source, baseline, companionPrefix }

def enrollment (find : Name → Option ConstantInfo) (owner : Name)
    (info : DefinitionVal) (source : String) : Except String TemplateEnrollmentInput := do
  let fs ← Literal.fields find ``Contract.TemplateEnrollment info.value 4
  let name ← compiledMetadata find fs[0]! (Literal.name "name")
  let args := info.type.getAppArgs
  unless args.size ≥ 2 && args[1]!.getAppFn.constName? == some name do
    throw s!"unclassified_form:contract.template_identity:{name}"
  rigidLevels info args[1]!
  discard <| compiledConstant find name
  let version ← compiledMetadata find fs[1]! (Literal.nat "nat")
  let constructors ← (← compiledArray find fs[2]!).mapM fun e => do
    let fs ← Literal.fields find ``Contract.TypeRef e 2
    let name ← compiledMetadata find fs[0]! (Literal.name "name")
    unless fs[1]!.getAppFn.constName? == some name do
      throw s!"unclassified_form:contract.constructor_identity:{name}"
    discard <| compiledConstant find name
    return name
  let options ← compiledMetadata find fs[3]! Literal.options
  return { owner, name, version, constructors, sourceText := source, options }

/-- Axiom closure is read from compiled dependencies by the caller; no proof
checking, environment access or row-function evaluation occurs here. -/
def readSeal (find : Name → Option ConstantInfo) (axioms : Array Name)
    (source : Name) (e : Expr) : Except String SealInput := do
  let fs ← Literal.fields find ``Contract.Seal e 3
  unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
    throw s!"IE-C009 ProofConstructionFailed: {source} unapproved axiom dependency"
  let catalogs ← (← compiledArray find fs[1]!).mapM fun value => do
    let cs ← Literal.fields find ``Contract.SealCatalog value 15
    let arenaName ← compiledMetadata find cs[0]! (Literal.name "seal.arena")
    let catalogId ← compiledMetadata find cs[1]! (Literal.name "seal.catalog")
    return ({ source, arenaName, catalogId, value } : CompiledSealCatalog)
  return { rootId := ← compiledMetadata find fs[0]! (Literal.name "seal.root")
           catalogs, options := ← compiledMetadata find fs[2]! Literal.options }

end LeanInformationAudit.Contract.Decoder
