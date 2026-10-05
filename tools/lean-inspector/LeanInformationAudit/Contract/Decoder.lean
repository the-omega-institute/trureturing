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

/-- Closed bodies retain no reference to their discarded let binding. -/
private def closedBody : Expr → Expr
  | .mdata _ body => closedBody body
  | value@(.letE _ _ _ body _) => if Literal.closed body then closedBody body else value
  | value => value

/-- Follow at most 4096 compiled definition references. Applications,
projections and recursors require computation and have no decoding route. -/
def referencedValue (value : Expr) (seen : NameSet := {}) : MetaM Expr := do
  let mut value := value
  let mut seen := seen
  for _ in [:4097] do
    value := closedBody value
    let .const name levels := value | return value
    let info ← getConstInfo name
    let .defnInfo definition := info | return value
    unless definition.safety == .safe && definition.levelParams.length == levels.length do
      throwError "contract.cannot_decode:{name}:unsafe_or_invalid_reference"
    if seen.contains name then throwError "contract.cannot_decode:{name}:reference_cycle"
    if seen.size >= 4096 then throwError "contract.cannot_decode:{name}:reference_work"
    value := definition.value.instantiateLevelParams definition.levelParams levels
    seen := seen.insert name
  throwError "contract.cannot_decode:reference_work"

def fields (name : Name) (e : Expr) (count : Nat) : MetaM (Array Expr) := do
  let .ctorInfo ctor ← getConstInfo (name.str "mk")
    | throwError "contract.literal:unknown_structure:{name}"
  let value ← referencedValue e
  let args ← liftLiteral <| Literal.constructor (name.str "mk")
    (ctor.numParams + count) name.toString value
  return args.extract ctor.numParams args.size

def metadata (value : Expr) (decode : Expr → Except String α) : MetaM α := do
  let resolved ← liftLiteral <| LeanInformationAudit.Contract.Literal.resolveReferences ((← getEnv).find? ·) value
  liftLiteral (decode resolved)

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
  let all ← fields ``Contract.Registration info.value 20
  let axioms ← collectAxioms info.name
  let trusted := axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·)
  let typeArgs := info.type.getAppArgs
  unless typeArgs.size == 5 do throwError "contract.registration:target_arity"
  let theoremName ← constantName "target" typeArgs[1]!
  discard <| checkTarget theoremName typeArgs[1]!
  rigidLevels info typeArgs[1]!
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

def expectedRow (e : Expr) : MetaM SnapshotOccurrence := do
  let fs ← fields ``Contract.ExpectedOccurrence e 6
  let theoremName ← metadata fs[2]! (Literal.name "name")
  let info ← checkTarget theoremName fs[1]!
  let objectArenaName ← metadata fs[3]! (Literal.name "name")
  discard <| getConstInfo objectArenaName
  let statementIdentity ← (← optional fs[4]!).mapM fun e =>
    metadata e (Literal.string "statement_identity")
  let registrationModuleName ← metadata fs[5]! (Literal.name "name")
  return {
    theoremName, objectArenaName
    statementIdentity := statementIdentity.getD ""
    capturedStatement := if statementIdentity.isSome then none else some info.type
    registrationModuleName }

def rootCatalog (e : Expr) : MetaM RootCatalogContract := do
  let outer ← fields ``Contract.RootCatalog e 1
  let fs ← fields ``Contract.RootCatalogData outer[0]! 5
  let rootId ← metadata fs[0]! (Literal.name "name")
  let expected ← (← arrayValues fs[1]!).mapM expectedRow
  let source ← (← arrayValues fs[2]!).mapM expectedRow
  let baseline ← (← arrayValues fs[3]!).mapM expectedRow
  let companionPrefix ← (← optional fs[4]!).mapM fun e =>
    metadata e (Literal.name "companion_prefix")
  return { rootId, expected, source, baseline, companionPrefix }

def enrollment (owner : Name) (info : DefinitionVal) (source : String) :
    MetaM TemplateEnrollmentInput := do
  let fs ← fields ``Contract.TemplateEnrollment info.value 4
  let name ← metadata fs[0]! (Literal.name "name")
  let args := info.type.getAppArgs
  unless args.size ≥ 2 && args[1]!.getAppFn.constName? == some name do
    throwError "unclassified_form:contract.template_identity:{name}"
  rigidLevels info args[1]!
  discard <| getConstInfo name
  let version ← metadata fs[1]! (Literal.nat "nat")
  let constructors ← (← arrayValues fs[2]!).mapM fun e => do
    let fs ← fields ``Contract.TypeRef e 2
    let name ← metadata fs[0]! (Literal.name "name")
    unless fs[1]!.getAppFn.constName? == some name do
      throwError "unclassified_form:contract.constructor_identity:{name}"
    discard <| getConstInfo name
    return name
  let options ← metadata fs[3]! Literal.options
  return { owner, name, version, constructors, sourceText := source, options }

def readSeal (source : Name) (e : Expr) : MetaM SealInput := do
  let fs ← fields ``Contract.Seal e 3
  let axioms ← collectAxioms source
  unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
    throwError "IE-C009 ProofConstructionFailed: {source} unapproved axiom dependency"
  let catalogs ← (← arrayValues fs[1]!).mapM fun value => do
    let cs ← fields ``Contract.SealCatalog value 15
    let arenaName ← metadata cs[0]! (Literal.name "seal.arena")
    let catalogId ← metadata cs[1]! (Literal.name "seal.catalog")
    return ({ source, arenaName, catalogId, value } : CompiledSealCatalog)
  return { rootId := ← metadata fs[0]! (Literal.name "seal.root")
           catalogs, options := ← metadata fs[2]! Literal.options }

end LeanInformationAudit.Contract.Decoder
