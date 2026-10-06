import LeanInformationAudit.CompiledSourceOperands
import LeanInformationAudit.Registry.Repository

namespace LeanInformationAudit.CompiledSourceFinite
open Lean CompiledSourceScope

private def fail [Monad m] [MonadLiftT IO m] (reason : String) : m α :=
  liftM (m := IO) (throw (IO.userError reason) : IO α)

private def constantReference (event : TemplateOccurrenceEvent) (name : Name) : M Expr := do
  let info ← getConstInfo name
  unless info.levelParams.length == event.levelParams.length do
    fail "contract.node_binding:source.finite_lift_levels"
  return mkConst name (event.levelParams.map Level.param)

private def abstractLambda (xs : Array Expr) (body : Expr) : M Expr := do
  let mut body := body
  for x in xs.reverse do
    let some binder := (← read).provenance.locals.find? x.fvarId!
      | fail "incomplete_closure:E7.compiled_local"
    body := .lam binder.userName binder.type (body.abstract #[x]) binder.binderInfo
  return body

private def family := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily
private def finite := `D5.S3.ConceptDynamics.InformationEscape

/-- The finite bridge is transported through a kernel-checked bijection and
 whole-family Law certificate. Its actual realization remains a bound operand. -/
def validate (event : TemplateOccurrenceEvent) (arena actual : Expr)
    (bridgeName liftName : Name) : M Unit := do
  let bridge ← constantReference event bridgeName
  let bridgeType ← projectType bridge
  unless bridgeType.isAppOfArity (finite ++ `LegacyPrimitiveRealization) 3 do
    fail "unclassified_form:source.finite_bridge"
  let certificate ← getConstInfo liftName
  unless certificate.levelParams.length == event.levelParams.length do
    fail "contract.node_binding:source.finite_lift_levels"
  let certificateType := Contract.Literal.instantiateRawLevels certificate.levelParams
    (event.levelParams.map Level.param) certificate.type
  unless certificateType.isAppOfArity `LeanInformationAudit.Contract.FiniteLiftFacts 4 do
    fail "contract.node_binding:source.finite_lift_type"
  let indices := certificateType.getAppArgs
  unless (← sameShape indices[0]! event.arena) && (← sameShape indices[1]! arena) do
    fail "contract.node_binding:source.finite_lift_arenas"
  let some value := certificate.value? | fail "contract.node_binding:source.finite_lift_definition"
  let value := Contract.Literal.instantiateRawLevels certificate.levelParams
    (event.levelParams.map Level.param) value
  let find := (← read).provenance.view.find?
  let fields ← IO.ofExcept <| Contract.Literal.fields find
    `LeanInformationAudit.Contract.FiniteLiftFacts value 4
  let observationTable ← IO.ofExcept <| Contract.Literal.resolveReferences find fields[3]!
  let observations ← IO.ofExcept <| Contract.Literal.list "finite_lift.observations" observationTable
  let context ← read
  let view : Contract.NodeFacts.View := {
    find, owner := context.provenance.view.ownerOf,
    external := fun n => context.extern n || context.implementedBy n }
  for observation in observations do
    let name ← IO.ofExcept <| Contract.Literal.name "finite_lift.observation" observation
    discard <| IO.ofExcept <| Contract.NodeFacts.fact view name
  unless ← sameShape actual (mkApp indices[2]! bridgeType.getAppArgs[2]!) do
    fail "contract.node_binding:source.finite_lift_actual"

end LeanInformationAudit.CompiledSourceFinite

namespace LeanInformationAudit.CompiledSourceContract
open Lean TemplateAudit CompiledSourceScope

private def fail [Monad m] [MonadLiftT IO m] (reason : String) : m α :=
  liftM (m := IO) (throw (IO.userError reason) : IO α)

private def fingerprintInput (params : List Name) (e : Expr) (fuel : Nat) :
    M (Except String (String × Nat)) := do
  let (erased, work) ← (RegistrationGates.eraseBoundProofs e fuel).run (← read).provenance
  return (compactRawIdentity params erased (fuel - work)).map fun (identity, cost) =>
    (identity, cost + work)

private def emit (message : String) : M Unit := do
  (← read).provenance.trace message

private def family := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily

private def atLevels (event : TemplateOccurrenceEvent) (name : Name) : M Expr := do
  debit
  let info ← getConstInfo name
  unless info.levelParams.length == event.levelParams.length do
    fail "unclassified_form:source.rigid_universes"
  return mkConst name (event.levelParams.map Level.param)

private def safe (name : Name) : M Unit := do
  debit
  let info ← getConstInfo name
  if info.isUnsafe || (← read).implementedBy name ||
      (← read).extern name then
    fail "forbidden_dependency:source.declaration_kind"
  let axioms ← (← read).collectAxioms name
  debit axioms.size
  unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
    fail "forbidden_dependency:source.axiom_closure"

private def fingerprint (levels : List Name) (e : Expr) : M String := do
  let (identity, work) ← match ← fingerprintInput levels e (← get) with
    | .ok result => pure result
    | .error reason => fail s!"{reason}:source_fingerprint={e.getAppFn.constName?.getD .anonymous}"
  debit work
  emit s!"source fingerprint identity={identity} work={work}"
  return identity

private def inputIdentity (name : Name) : M DependencyIdentity := do
  debit
  let info ← getConstInfo name
  let owner ← ownerOf name
  let typeIdentity ← fingerprint info.levelParams info.type
  -- Source-opaque operands use the compiled owner identity. Only repository
  -- data bodies contribute another fingerprint.
  let bodyIdentity ← if !(← isProp info.type) && Repository.isModule owner then
      match info.value? with
      | some value => fingerprint info.levelParams value
      | none => pure ""
    else pure ""
  return { name, owner, typeIdentity, bodyIdentity }

/-- Fixed source-bound branch of the shared assessor. No callback or additional
registry can manufacture a checked plan or a binding certificate. -/
def validate (event : TemplateOccurrenceEvent) (descriptor : Expr)
    (plan : TemplatePlanData) (input : EscapeRecordInput) : ReaderT Context IO TemplateBindingCertificate := do
  let limit := min 524288 (informationTemplate.work.get (← read).provenance.options)
  let action : M TemplateBindingCertificate := do
    debit plan.serializedBytes
    let some selection := input.sourceSelection | fail "unclassified_form:source.selection_missing"
    unless input.fromObject.isNone && input.continuation.isNone && input.openContinuation do
      fail "unclassified_form:source.residual_requires_open"
    let original ← getConstInfo event.key.theoremName
    let .thmInfo theoremInfo := original | fail "unclassified_form:source.theorem"
    unless theoremInfo.levelParams.length == event.levelParams.length do
      fail "contract.node_binding:source.theorem_levels"
    let instantiate := Contract.Literal.instantiateRawLevels theoremInfo.levelParams
      (event.levelParams.map Level.param)
    let info : ConstantInfo := .thmInfo { theoremInfo with
      levelParams := event.levelParams, type := instantiate theoremInfo.type,
      value := instantiate theoremInfo.value }
    let scope ← resolve info selection
    emit s!"source phase=resolve work={limit - (← get)}"
    let objectArena ← atLevels event event.key.objectArena
    let record ← atLevels event event.realizationName
    if let some definition := scope.definition then safe definition.name
    safe event.key.theoremName
    safe event.realizationName
    safe event.key.objectArena
    let type ← projectType record
    unless type.isAppOfArity (family ++ `Registration) 2 do
      fail "unclassified_form:source.record_statement"
    if event.compiledMathematics.isNone then
      unless ← sameShape type.getAppArgs[1]! info.type do
        fail "unclassified_form:source.record_statement"
    let arena := type.getAppArgs[0]!
    let some arenaName := arena.constName? | fail "unclassified_form:source.arena_identity"
    unless arena.equal (← atLevels event arenaName) do
      fail "unclassified_form:source.arena_identity"
    safe arenaName
    if input.finiteBridge.isNone then
      unless ← sameShape arena objectArena do fail "unclassified_form:source.record_statement"
    let actual ← projectField (family ++ `Registration.actual) record
    let signature ← projectField (family ++ `Arena.signature) arena
    let law := mkApp2 (mkConst (family ++ `Arena.Law) arena.constLevels!) arena
      (mkAppN (mkConst (family ++ `Registration.actual) record.constLevels!)
        #[arena, type.getAppArgs[1]!, record])
    unless ← sameShape info.type law do fail "unclassified_form:source.statement_bridge_fact"
    let some roleEnumeration := input.roleEnumeration
      | fail "unclassified_form:source.role_enumeration_missing"
    let roles ← enumeration roleEnumeration (← projectField (family ++ `Signature.Role) signature)
    let some anchorEnumeration := input.anchorEnumeration
      | fail "unclassified_form:source.anchor_enumeration_missing"
    discard <| enumeration anchorEnumeration (← projectField (family ++ `Signature.Anchor) signature)
    validateFields scope actual event.key.theoremName roles
    if let some bridge := input.finiteBridge then
      safe bridge
      let some finiteLift := input.finiteLift | fail "unclassified_form:source.finite_lift_missing"
      safe finiteLift
      CompiledSourceFinite.validate event arena actual bridge finiteLift
    emit s!"source phase=reconstruction_and_fields work={limit - (← get)}"
    discard <| normalizeHead actual
    -- Inspect every raw supplied operand before shape comparison.
    let recordInfo ← getConstInfo event.realizationName
    let some value := recordInfo.value? | fail "unclassified_form:source.record_definition"
    let value := (Contract.Literal.instantiateRawLevels recordInfo.levelParams
      (event.levelParams.map Level.param) value).consumeMData
    unless value.isAppOfArity (family ++ `Registration.mk) 7 do
      fail "unclassified_form:source.record_literal"
    let rawActual := value.getAppArgs[2]!
    let lawFunction ← projectField (family ++ `Arena.Law) arena
    let (_, work) ← (CompiledSourceOperands.check event.key.theoremName
      #[descriptor, rawActual] (← get) (some (record, lawFunction))
      (scope.definition.map (·.value))
      (if input.finiteBridge.isSome then some objectArena else none) input.exclusion
      (some (event.levelParams.map Level.param))).run (← read)
    debit work
    emit s!"source phase=operands work={limit - (← get)}"
    unless ← sameShape descriptor rawActual do fail "unclassified_form:source.descriptor_actual"
    let actualIdentity ← fingerprint scope.levels rawActual
    let descriptorIdentity ← fingerprint scope.levels descriptor
    let registrationIdentity ← fingerprint scope.levels record
    let sourceTypeIdentity ← match compactRawIdentity scope.levels info.type (← get) with
      | .ok (identity, work) => debit work; pure identity
      | .error reason => fail reason
    let readouts ← scope.readouts.mapIdxM fun i readout => do
      let selected := selection.readouts[i]!
      let closed := readout.rawContext.foldr (fun b e =>
        if let some v := b.value then Expr.letE b.name b.domain v e b.nondep
        else Expr.lam b.name b.domain e b.info) readout.rawObservation
      let modes := if selected.functionOperand then [("function_operand", toJson true)]
        else if let some path := selected.stateOperand then
          [("state_operand", toJson path), ("boolean_predicate", toJson selected.booleanPredicate)]
        else []
      return Json.mkObj ([
        ("path", toJson selected.path), ("state_binder", toJson selected.stateBinder),
        ("scope_size", toJson readout.rawContext.size),
        ("scope_paths", toJson (readout.rawContext.map (·.path))),
        ("occurrence_identity", toJson (← fingerprint scope.levels closed))] ++ modes)
    let definitionInput : Option DependencyIdentity ← match scope.definition with
      | none => pure none
      | some definition => do
        let rawFingerprint := fun e => do
          let .ok (identity, work) := compactRawIdentity scope.levels e (← get)
            | fail "incomplete_closure:E8.source_definition_fingerprint"
          debit work
          pure identity
        let typeIdentity ← rawFingerprint definition.type
        let bodyIdentity ← rawFingerprint definition.value
        pure (some {
          name := definition.name
          owner := definition.owner
          typeIdentity := typeIdentity
          bodyIdentity := bodyIdentity })
    let definitionEntry ← definitionInput.toList.mapM fun entry => do
      let reference := mkConst entry.name (scope.levels.map Level.param)
      let .ok (referenceIdentity, work) := compactRawIdentity scope.levels reference (← get)
        | fail "incomplete_closure:E8.source_definition_reference_fingerprint"
      debit work
      pure ("definition_entry", Json.mkObj [
        ("reference_identity", toJson referenceIdentity),
        ("path", toJson (scope.definition.map (·.path) |>.getD #[])),
        ("owner", toJson entry.owner.toString),
        ("name", toJson entry.name.toString),
        ("type_identity", toJson entry.typeIdentity),
        ("body_identity", toJson entry.bodyIdentity)])
    let projection := input.finiteBridge.toList.map fun bridge =>
      ("finite_projection", Json.mkObj [
        ("family_arena", toJson arenaName.toString), ("bridge", toJson bridge.toString)])
    let sourceBinding := Json.mkObj ([
      ("source_owner", toJson selection.owner.toString),
      ("source_name", toJson event.key.theoremName.toString),
      ("source_type_identity", toJson sourceTypeIdentity),
      ("telescope_size", toJson scope.telescope.size),
      ("level_count", toJson scope.levels.length),
      ("coordinates", toJson selection.coordinates),
      ("coordinate_paths", toJson (scope.coordinates.map (·.path))),
      ("readouts", Json.arr readouts), ("registration_identity", toJson registrationIdentity)] ++
      definitionEntry ++ projection)
    let escape : EscapeRecordEvidence := {
      bridgeKind := "source-equivalence"
      fromObject := some {
        name := event.key.theoremName
        typeIdentity := sourceTypeIdentity
        objectIdentity := actualIdentity }
      continuation := some { kind := "open" } }
    emit s!"source phase=identities work={limit - (← get)}"
    let roots := #[event.key.theoremName, event.realizationName, event.key.objectArena, arenaName] ++
      input.finiteBridge.toArray
    let mut extractionInputs ← roots.toList.eraseDups.toArray.mapM inputIdentity
    if let some entry := definitionInput then
      extractionInputs := extractionInputs.push entry
    let certificate : TemplateBindingCertificate := {
      evidenceRef := "", key := event.key, planIdentity := plan.planIdentity,
      descriptorIdentity, actualIdentity, argumentInputs := #[], extractionInputs,
      escape, sourceBinding := some sourceBinding }
    let .ok (evidenceRef, work) := bindingIdentity event.statementIdentity certificate (← get)
      | fail "incomplete_closure:E8.source_evidence"
    debit work
    emit s!"source contract work={limit - (← get)} telescope={scope.telescope.size} roles={scope.readouts.size}"
    return { certificate with evidenceRef }
  let (certificate, _) ← action.run limit
  return certificate

end LeanInformationAudit.CompiledSourceContract
