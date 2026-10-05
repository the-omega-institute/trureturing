import LeanInformationAudit.Registry
import LeanInformationAudit.Contract.Literal
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
def referencedValue (value : Expr) (seen : NameSet := {}) : MetaM Expr := do
  liftLiteral <| Literal.referencedValue ((← getEnv).find? ·) value seen

def fields (name : Name) (e : Expr) (count : Nat) : MetaM (Array Expr) := do
  liftLiteral <| Literal.fields ((← getEnv).find? ·) name e count

def compiledMetadata (find : Name → Option ConstantInfo) (value : Expr)
    (decode : Expr → Except String α) : Except String α := do
  decode (← Literal.resolveReferences find value)

def metadata (value : Expr) (decode : Expr → Except String α) : MetaM α := do
  liftLiteral <| compiledMetadata ((← getEnv).find? ·) value decode

private def constantName (role : String) (value : Expr) : MetaM Name := do
  liftLiteral <| Literal.constantName ((← getEnv).find? ·) role value

/-- Recover payload identity from its compiled constant head without reduction. -/
def reference (role : String) (e : Expr) : MetaM (Name × Expr) := do
  liftLiteral <| Literal.reference ((← getEnv).find? ·) role e

private def optional (e : Expr) : MetaM (Option Expr) := do
  liftLiteral <| Literal.optional "option" (← referencedValue e)

private def optionalRef (role : String) (e : Expr) : MetaM (Option (Name × Expr)) := do
  (← optional e).mapM (reference role)

/-- Read an indexed obligation's constructor and the original submitted name.
The proof field was checked when its containing Reg declaration compiled. -/
private def obligation (e : Expr) : MetaM (CompiledObligationState × Option (Name × Expr)) := do
  let e := e.consumeMData
  if e.isAppOf ``Contract.Obligation.evidence then
    let args := e.getAppArgs
    return (.evidence, some (← reference "obligation" args[args.size - 2]!))
  if e.isAppOf ``Contract.Obligation.unsupported then
    let name ← metadata e.getAppArgs.back! (Literal.name "obligation.unsupported")
    return (.unsupported, some (name, mkConst name))
  if e.isAppOf ``Contract.Obligation.unknown then return (.unknown, none)
  if e.isAppOf ``Contract.Obligation.absent then return (.absent, none)
  throwError "contract.literal:obligation"

private def obligationState (e : Expr) : MetaM CompiledObligationState := do
  let head := e.consumeMData.getAppFn.constName?
  if head == some ``Contract.Obligation.evidence || head == some ``Contract.ExactMatch.evidence then return .evidence
  if head == some ``Contract.Obligation.unsupported || head == some ``Contract.ExactMatch.unsupported then return .unsupported
  if head == some ``Contract.Obligation.unknown || head == some ``Contract.ExactMatch.unknown then return .unknown
  if head == some ``Contract.Obligation.absent || head == some ``Contract.ExactMatch.absent then return .absent
  throwError "contract.literal:obligation"

private def arenaReference (role : String) (e : Expr) : MetaM (Name × Expr) := do
  let head := e.consumeMData.getAppFn.constName?.getD .anonymous
  unless #[``Contract.ArenaRef.law, ``Contract.ArenaRef.finite, ``Contract.ArenaRef.object,
      ``Contract.ArenaRef.witness, ``Contract.ArenaRef.source].contains head do
    throwError "contract.literal:arena:{role}"
  reference role e.getAppArgs.back!

private def arrayValues (e : Expr) : MetaM (Array Expr) := do
  liftLiteral <| Literal.array "array" (← referencedValue e)

private def sourceSelection (e : Expr) : MetaM LeanInformationAudit.SourceSelection := do
  let s ← metadata e Literal.sourceSelection
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

def registration (owner : Name) (info : DefinitionVal) (source : String)
    : MetaM CompanionInput := do
  let all ← fields ``Contract.Registration info.value 20
  let axioms ← collectAxioms info.name
  let trusted := axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·)
  let typeArgs := info.type.getAppArgs
  unless typeArgs.size == 5 do throwError "contract.registration:target_arity"
  let theoremName ← constantName "target" typeArgs[1]!
  discard <| liftLiteral <| checkTarget ((← getEnv).find? ·) theoremName typeArgs[1]!
  liftLiteral <| rigidLevels info typeArgs[1]!
  let fs := all.extract 4 all.size
  let (arenaName, _) ← arenaReference "arena" fs[0]!
  let (objectArenaName, _) ← arenaReference "object_arena" fs[1]!
  unless !arenaName.isAnonymous && !objectArenaName.isAnonymous do
    throwError "contract.registration:arena_identity"
  let catalog ← metadata fs[2]! (Literal.name "catalog")
  let localNames ← metadata fs[3]! (Literal.bool "local_names")
  let implementation := fs[4]!.consumeMData
  let head := implementation.getAppFn.constName?.getD .anonymous
  unless #[``Contract.Implementation.legacy, ``Contract.Implementation.forward,
      ``Contract.Implementation.witness, ``Contract.Implementation.source].contains head do
    throwError "contract.literal:implementation:nonliteral:{head}"
  let implementationArgs := implementation.getAppArgs
  let sourceBound := head == ``Contract.Implementation.source
  let witness := head == ``Contract.Implementation.witness
  let expectedArity := if sourceBound then 3 else if witness then 10 else 7
  unless implementationArgs.size == expectedArity do
    throwError "contract.registration:implementation_arity"
  let bridgeField := implementationArgs[if sourceBound then 2 else 4]!
  let (suppliedName, bridge) ← reference "realization" bridgeField
  let occurrence := !sourceBound && !localNames
  let family ← (← optional fs[14]!).mapM fun e =>
    reference "family_record" e.getAppArgs.back!
  let unitName ← metadata all[0]! (Literal.name "unit_name")
  let realizationName ← metadata all[1]! (Literal.name "realization_name")
  let realizationSource ← (← optional all[2]!).mapM fun e =>
    metadata e (Literal.name "realization_source")
  if realizationSource.any (· != suppliedName) then
    throwError "contract.registration:realization_source_identity"
  let generated ← metadata all[3]! (Literal.bool "generated")
  unless !unitName.isAnonymous && !realizationName.isAnonymous do
    throwError "contract.registration:companion_identity"
  if sourceBound && (generated || realizationName != suppliedName) then
    throwError "contract.registration:source_bridge_identity"
  let descriptor ← optional fs[7]!
  let primitives := if sourceBound then none else some
    implementationArgs[3]!
  let positive := if witness then some implementationArgs[5]! else none
  let (unit, unitCorrespondence) ← if sourceBound then pure (none, true) else do
    let bound ← fields ``Contract.BoundTheoremUnit implementationArgs.back! 3
    let value ← fields ``Contract.Ref bound[0]! 1
    pure (some value[0]!, (← obligationState bound[1]!) == .evidence &&
      (← obligationState bound[2]!) == .evidence &&
      (← obligationState implementationArgs[if witness then 8 else 5]!) == .evidence)
  let (variationState, variation, witnessPositive, witnessNegative) ← if witness then do
    let parts ← fields ``Contract.Implementation.WitnessVariationEvidence fs[8]! 2
    let (positiveState, positiveInput) ← obligation parts[0]!
    let (negativeState, negativeInput) ← obligation parts[1]!
    pure (if positiveState == .evidence then negativeState else positiveState,
      positiveInput.or negativeInput, positiveState, negativeState)
  else do
    let (state, value) ← obligation fs[8]!
    pure (state, value, .evidence, .evidence)
  let (sensitivityState, sensitivity) ← obligation fs[9]!
  let partialEvidence ← (← optional fs[10]!).mapM fun e => do
    if sourceBound then throwError "contract.sensitivity:finite_slots_required"
    let values ← fields ``Contract.Implementation.PartialSlotEvidence e 2
    let arena ← if witness then do
        pure (← RegistrationElaboration.normalizeArena implementationArgs[1]!).law
      else pure implementationArgs[1]!
    let sig ← mkAppM ``PrimitiveLawArena.signature #[arena]
    let states (fn indexType fintype : Expr) := do
      let domain ← whnf (← inferType fn).bindingDomain!
      unless domain.isAppOf ``ULift do throwError "contract.sensitivity:index_carrier"
      let slots ← RegistrationGates.indices indexType fintype
      slots.mapM fun index => do
        let lifted := mkAppN (mkConst ``ULift.up domain.getAppFn.constLevels!) (domain.getAppArgs.push index)
        return (← obligationState (← whnf (mkApp fn lifted))) == .evidence
    let readouts ← states values[0]! (← mkAppM ``PrimitiveSignature.Index #[sig])
      (← mkAppM ``PrimitiveSignature.indexFintype #[sig])
    let anchors ← states values[1]! (← mkAppM ``PrimitiveSignature.AnchorIndex #[sig])
      (← mkAppM ``PrimitiveSignature.anchorFintype #[sig])
    return (readouts, anchors)
  let origin ← optional fs[11]!
  let selection ← (← optional fs[12]!).mapM sourceSelection
  let (openContinuation, residual) ← continuation fs[13]!
  let options ← metadata fs[15]! Literal.options
  let correspondenceFields ← fields ``Contract.Implementation.Correspondence fs[5]! 2
  let stage ← obligationState correspondenceFields[0]!
  let objectStage ← obligationState correspondenceFields[1]!
  let correspondence := if stage == .evidence && objectStage == .evidence then .evidence else .unsupported
  let witnessActual ← if witness then obligationState implementationArgs[6]! else pure .evidence
  let witnessStatement ← if witness then obligationState implementationArgs[7]! else pure .evidence
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
      witness, correspondence := if unitCorrespondence && trusted then correspondence else .unsupported,
      bundleNonempty := ← obligationState fs[6]!,
      variation := variationState, sensitivity := sensitivityState,
      witnessPositive, witnessNegative, witnessActual, witnessStatement,
      partialReadouts := partialEvidence.map Prod.fst, partialAnchors := partialEvidence.map Prod.snd } }
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
