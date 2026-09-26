import LeanInformationAudit.Registry.SourceOperands

namespace LeanInformationAudit.SourceContract
open Lean Meta TemplateAudit SourceScope

private def family := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily

private def atLevels (event : TemplateOccurrenceEvent) (name : Name) : M Expr := do
  debit
  let info ← getConstInfo name
  unless info.levelParams.length == event.levelParams.length do
    throwError "unclassified_form:source.rigid_universes"
  return mkConst name (event.levelParams.map Level.param)

private def safe (name : Name) : M Unit := do
  debit
  let info ← getConstInfo name
  if info.isUnsafe || (Compiler.getImplementedBy? (← getEnv) name).isSome ||
      (getExternAttrData? (← getEnv) name).isSome then
    throwError "forbidden_dependency:source.declaration_kind"
  let axioms ← collectAxioms name
  debit axioms.size
  unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
    throwError "forbidden_dependency:source.axiom_closure"

private def fingerprint (levels : List Name) (e : Expr) : M String := do
  let .ok (identity, work) ← compactIdentity levels e (← get)
    | throwError "incomplete_closure:E8.source_fingerprint"
  debit work
  trace[InformationRegistration.check] "source fingerprint identity={identity} work={work}"
  return identity

private def inputIdentity (name : Name) : M DependencyIdentity := do
  debit
  let info ← getConstInfo name
  let owner := (RegistrationReifier.declaringModuleOf (← getEnv) name).getD
    (← getEnv).header.mainModule
  let typeIdentity ← fingerprint info.levelParams info.type
  -- Source-opaque operands need no duplicated upstream body fingerprint.
  -- The owning imported image is validated by the existing native coherence gate.
  let bodyIdentity ← if !(← isProp info.type) && Repository.isModule owner then
      match info.value? with
      | some value => fingerprint info.levelParams value
      | none => pure ""
    else pure ""
  return { name, owner, typeIdentity, bodyIdentity }

/-- Fixed source-bound branch of the shared assessor. No callback or additional
registry can manufacture a checked plan or a binding certificate. -/
def validate (event : TemplateOccurrenceEvent) (descriptor : Expr)
    (plan : TemplatePlanData) (input : EscapeRecordInput) : MetaM TemplateBindingCertificate := do
  let limit := min 524288 (informationTemplate.work.get (← getOptions))
  let action : M TemplateBindingCertificate := do
    debit plan.serializedBytes
    let some selection := input.sourceSelection | throwError "unclassified_form:source.selection_missing"
    unless input.fromObject.isNone && input.continuation.isNone && input.openContinuation do
      throwError "unclassified_form:source.residual_requires_open"
    let info ← getConstInfo event.key.theoremName
    let scope ← resolve info selection
    trace[InformationRegistration.check] "source phase=resolve work={limit - (← get)}"
    let arena ← atLevels event event.key.objectArena
    let record ← atLevels event event.realizationName
    if let some definition := scope.definition then safe definition.name
    safe event.key.theoremName
    safe event.realizationName
    safe event.key.objectArena
    let type ← inferType record
    unless type.isAppOfArity (family ++ `Registration) 2 &&
        type.getAppArgs[0]!.equal arena && (← isDefEq type.getAppArgs[1]! info.type) do
      throwError "unclassified_form:source.record_statement"
    let actual ← mkAppM (family ++ `Registration.actual) #[record]
    let signature ← mkAppM (family ++ `Arena.signature) #[arena]
    let law ← mkAppM (family ++ `Arena.Law) #[arena, actual]
    reconstruct scope.expanded law
    validateFields scope signature actual
    trace[InformationRegistration.check] "source phase=reconstruction_and_fields work={limit - (← get)}"
    checkWithKernel record
    let obligations := #[
      (`bridge, mkApp2 (mkConst ``Iff) info.type law),
      (`variation, ← mkAppM (family ++ `Variation) #[arena, actual]),
      (`sensitivity, ← mkAppM (family ++ `Sensitivity) #[arena, actual]),
      (`dependence, ← mkAppM (family ++ `ObservationalDependence) #[signature, actual])]
    for (name, expected) in obligations do
      let proof ← mkAppM (family ++ `Registration ++ name) #[record]
      unless ← isDefEq (← inferType proof) expected do
        throwError "unclassified_form:source.proof_obligation:{name}"
      checkWithKernel proof
    let actual ← whnf actual
    -- Inspect every raw supplied operand before defeq can discard arguments.
    let recordInfo ← getConstInfo event.realizationName
    let some value := recordInfo.value? | throwError "unclassified_form:source.record_definition"
    let value := (value.instantiateLevelParams recordInfo.levelParams
      (event.levelParams.map Level.param)).consumeMData
    unless value.isAppOfArity (family ++ `Registration.mk) 7 do
      throwError "unclassified_form:source.record_literal"
    let rawActual := value.getAppArgs[2]!
    let lawFunction ← mkAppM (family ++ `Arena.Law) #[arena]
    let (_, work) ← SourceOperands.check event.key.theoremName
      #[descriptor, rawActual] (← get) (some lawFunction)
      (scope.definition.map (·.value))
    debit work
    trace[InformationRegistration.check] "source phase=operands work={limit - (← get)}"
    unless ← isDefEq descriptor rawActual do throwError "unclassified_form:source.descriptor_actual"
    let actualIdentity ← fingerprint scope.levels rawActual
    let descriptorIdentity ← fingerprint scope.levels descriptor
    let registrationIdentity ← fingerprint scope.levels record
    let sourceTypeIdentity ← match compactRawIdentity scope.levels info.type (← get) with
      | .ok (identity, work) => debit work; pure identity
      | .error reason => throwError reason
    let readouts ← scope.readouts.mapIdxM fun i readout => do
      let selected := selection.readouts[i]!
      let closed := readout.context.foldr (fun b e =>
        if let some v := b.value then Expr.letE b.name b.domain v e b.nondep
        else Expr.forallE b.name b.domain e b.info) readout.observation
      return Json.mkObj [
        ("path", toJson selected.path), ("state_binder", toJson selected.stateBinder),
        ("scope_size", toJson readout.context.size),
        ("scope_paths", toJson (readout.context.map (·.path))),
        ("occurrence_identity", toJson (← fingerprint scope.levels closed))]
    let definitionInput : Option DependencyIdentity ← match scope.definition with
      | none => pure none
      | some definition => do
        let rawFingerprint := fun e => do
          let .ok (identity, work) := compactRawIdentity scope.levels e (← get)
            | throwError "incomplete_closure:E8.source_definition_fingerprint"
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
        | throwError "incomplete_closure:E8.source_definition_reference_fingerprint"
      debit work
      pure ("definition_entry", Json.mkObj [
        ("reference_identity", toJson referenceIdentity),
        ("path", toJson (scope.definition.map (·.path) |>.getD #[])),
        ("owner", toJson entry.owner.toString),
        ("name", toJson entry.name.toString),
        ("type_identity", toJson entry.typeIdentity),
        ("body_identity", toJson entry.bodyIdentity)])
    let sourceBinding := Json.mkObj ([
      ("source_owner", toJson selection.owner.toString),
      ("source_name", toJson event.key.theoremName.toString),
      ("source_type_identity", toJson sourceTypeIdentity),
      ("telescope_size", toJson scope.telescope.size),
      ("level_count", toJson scope.levels.length),
      ("coordinates", toJson selection.coordinates),
      ("coordinate_paths", toJson (scope.coordinates.map (·.path))),
      ("readouts", Json.arr readouts), ("registration_identity", toJson registrationIdentity)] ++
      definitionEntry)
    let escape : EscapeRecordEvidence := {
      bridgeKind := "source-equivalence"
      fromObject := some {
        name := event.key.theoremName
        typeIdentity := sourceTypeIdentity
        objectIdentity := actualIdentity }
      continuation := some { kind := "open" } }
    trace[InformationRegistration.check] "source phase=identities work={limit - (← get)}"
    let mut extractionInputs ← #[event.key.theoremName, event.realizationName,
      event.key.objectArena].mapM inputIdentity
    if let some entry := definitionInput then
      extractionInputs := extractionInputs.push entry
    let certificate : TemplateBindingCertificate := {
      evidenceRef := "", key := event.key, planIdentity := plan.planIdentity,
      descriptorIdentity, actualIdentity, argumentInputs := #[], extractionInputs,
      escape, sourceBinding := some sourceBinding }
    let .ok (evidenceRef, work) := bindingIdentity event.statementIdentity certificate (← get)
      | throwError "incomplete_closure:E8.source_evidence"
    debit work
    trace[InformationRegistration.check] "source contract work={limit - (← get)} telescope={scope.telescope.size} roles={scope.readouts.size}"
    return { certificate with evidenceRef }
  let (certificate, _) ← action.run limit
  NativeCoherence.validate (#[plan.definitionOwner, plan.enrollmentOwner,
    event.key.registrationModule] ++ certificate.extractionInputs.map (·.owner))
  return certificate

end LeanInformationAudit.SourceContract
