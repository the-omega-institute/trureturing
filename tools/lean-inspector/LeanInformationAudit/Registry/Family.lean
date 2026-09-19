import LeanInformationAudit.Registry.SourceScope

namespace LeanInformationAudit.FamilyRegistration
open Lean Meta TemplateAudit DependentFamily

private abbrev M := StateT Nat MetaM
private def debit (n : Nat := 1) : M Unit := do
  Core.checkMaxHeartbeats "family registration"
  unless n ≤ (← get) do throwError "incomplete_closure:E8.family_registration_work"
  modify (· - n)

private def rawId (params : List Name) (e : Expr) : M String := do
  let .ok (identity, work) := rawStatementIdentity params e (← get)
    | throwError "incomplete_closure:E8.family_identity"
  debit work
  return identity

private def atSourceLevels (event : TemplateOccurrenceEvent) (name : Name) : M Expr := do
  debit
  let info ← getConstInfo name
  unless info.levelParams.length == event.levelParams.length do
    throwError "unclassified_form:family.registration.rigid_levels"
  return mkConst name (event.levelParams.map Level.param)

private def safeDeclaration (name : Name) : M Unit := do
  debit
  let info ← getConstInfo name
  if info.isUnsafe || (Compiler.getImplementedBy? (← getEnv) name).isSome ||
      (getExternAttrData? (← getEnv) name).isSome then
    throwError "unclassified_form:family.registration.declaration_kind"
  let axioms ← collectAxioms name
  debit axioms.size
  unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
    throwError "unclassified_form:family.registration.axiom_closure"

/-- Only the literal typed Registration constructor is extracted. Its proof
fields are checked as complete propositions, never classified as executables. -/
private def extractM (event : TemplateOccurrenceEvent) : M Expr := do
  let info ← getConstInfo event.realizationName
  let .defnInfo definition := info
    | throwError "unclassified_form:family.registration.record_definition"
  if (← isRecursiveDefinition info.name) || definition.all.length != 1 then
    throwError "unclassified_form:family.registration.record_definition"
  unless info.levelParams.length == event.levelParams.length do
    throwError "unclassified_form:family.registration.rigid_levels"
  let .ok (value, work) := PlanTransform.instantiateExpr definition.value info.levelParams
      (event.levelParams.map Level.param) (← get)
    | throwError "incomplete_closure:E8.family_registration_levels"
  debit work
  let value := value.consumeMData
  unless value.isAppOfArity ``Registration.mk 6 do
    throwError "unclassified_form:family.registration.literal_record"
  return value.getAppArgs[2]!

def extract (event : TemplateOccurrenceEvent) (fuel : Nat) : MetaM (Expr × Nat) := do
  let limit := min fuel 524288
  let (value, remaining) ← (extractM event).run limit
  return (value, limit - remaining)

private def contextId (scope : FamilySourceScope) (context : Array FamilySourceBinder)
    (body : Expr) : M String := rawId scope.levels (FamilySource.close context body)

private def sourceMaterial (event : TemplateOccurrenceEvent) (scope : FamilySourceScope)
    (record arena realization : Expr) : M Json := do
  let info ← getConstInfo event.key.theoremName
  let env ← getEnv
  let sourceOwner := (RegistrationReifier.declaringModuleOf env info.name).getD env.header.mainModule
  let source ← readSourceInput (sourcePath sourceOwner)
  let binders ← scope.telescope.mapIdxM fun i b => do
    debit
    return Json.mkObj [
      ("ordinal", toJson i), ("binder_info", toJson (reprStr b.info)),
      ("domain_identity", toJson (← contextId scope (scope.telescope.extract 0 i) b.domain))]
  let occurrence (o : FamilySourceOccurrence) (fiber : Expr) : M Json := do
    let context ← contextId scope o.context (mkSort .zero)
    let raw ← contextId scope o.context o.raw
    let projected ← rawId scope.levels (scope.coordinateDomains.foldr
      (fun b e => Expr.lam b.name b.domain e b.info) fiber)
    return Json.mkObj [("path", toJson o.path), ("context_identity", toJson context),
      ("raw_identity", toJson raw), ("fiber_identity", toJson projected),
      ("context_size", toJson o.context.size)]
  let signature ← mkAppM ``Arena.signature #[arena]
  let field (name : Name) : M String := do
    let value ← mkAppM name #[record]
    rawId scope.levels (.letE name (← inferType value) value (.bvar 0) false)
  return Json.mkObj [
    ("mode", toJson event.key.mode.wireName),
    ("source_name", toJson info.name.toString),
    ("source_path", toJson source.path), ("source_sha256", toJson source.sha256),
    ("statement_identity", toJson event.statementIdentity),
    ("source_type_identity", toJson (← rawId scope.levels scope.sourceType)),
    ("rigid_levels", toJson (scope.levels.map Name.toString)),
    ("telescope", Json.arr binders), ("coordinates", toJson scope.selection.coordinates),
    ("state", ← occurrence scope.state scope.stateFiber),
    ("output", ← occurrence scope.output scope.outputFiber),
    ("signature_identity", toJson (← rawId scope.levels signature)),
    ("state_field_identity", toJson (← rawId scope.levels (← mkAppM ``Signature.State #[signature]))),
    ("output_field_identity", toJson (← rawId scope.levels (← mkAppM ``Signature.Output #[signature]))),
    ("law_identity", toJson (← rawId scope.levels (← mkAppM ``Arena.Law #[arena]))),
    ("realization_identity", toJson (← rawId scope.levels realization)),
    ("registration_identity", toJson (← rawId scope.levels record)),
    ("bridge_identity", toJson (← field ``Registration.bridge)),
    ("variation_identity", toJson (← field ``Registration.variation)),
    ("sensitivity_identity", toJson (← field ``Registration.sensitivity)),
    ("continuation", toJson "open")]

/-- No finite-state validation or catalog adapter is called on this route. -/
def validate (event : TemplateOccurrenceEvent) (input : EscapeRecordInput)
    (fuel : Nat := 524288) : MetaM (EscapeRecordEvidence × Nat) := do
  let limit := min fuel 524288
  let action : M EscapeRecordEvidence := do
    unless event.key.mode == .dependentFamily do throwError "unclassified_form:family.mode"
    let some scope := event.familyScope | throwError "unclassified_form:family.source.missing"
    unless input.fromObject.isNone && input.continuation.isNone && input.openContinuation do
      throwError "unclassified_form:family.continuation.literal_open"
    let source ← getConstInfo event.key.theoremName
    unless source.isTheorem do throwError "unclassified_form:family.source.theorem"
    debit (← FamilySource.validate source scope (← get))
    let arena ← atSourceLevels event event.key.objectArena
    let record ← atSourceLevels event event.realizationName
    let proof := mkConst source.name (event.levelParams.map Level.param)
    safeDeclaration source.name
    safeDeclaration event.realizationName
    safeDeclaration event.key.objectArena
    checkWithKernel proof
    checkWithKernel record
    let type ← inferType record
    unless type.isAppOfArity ``Registration 2 do
      throwError "unclassified_form:family.registration.interface"
    let args := type.getAppArgs
    unless args[0]!.equal arena && (← isDefEq args[1]! event.statement) do
      throwError "unclassified_form:family.registration.source_law"
    let signature ← mkAppM ``Arena.signature #[arena]
    debit (← FamilySource.validateFields scope signature (← get))
    let realization ← extractM event
    let realizationType ← mkAppM ``Realization #[signature]
    unless ← isDefEq (← inferType realization) realizationType do
      throwError "unclassified_form:family.registration.realization"
    let law ← mkAppM ``Arena.Law #[arena, realization]
    unless ← isDefEq law event.statement do
      throwError "unclassified_form:family.registration.exact_source_law"
    let bridge ← mkAppM ``Registration.bridge #[record]
    let conclusion := mkApp bridge proof
    unless ← isDefEq (← inferType conclusion) law do
      throwError "unclassified_form:family.registration.bridge"
    checkWithKernel conclusion
    for (field, predicate) in #[(``Registration.variation, ``GlobalFamilyVariation),
        (``Registration.sensitivity, ``FamilyRoleSensitivity)] do
      let witness ← mkAppM field #[record]
      let expected ← mkAppM predicate #[arena]
      unless ← isDefEq (← inferType witness) expected do
        throwError "unclassified_form:family.registration.witness_scope"
      checkWithKernel witness
    let material ← sourceMaterial event scope record arena realization
    let bytes := ("DTR-family-evidence-v1\x00" ++ material.compress).toUTF8
    debit bytes.size
    let family := { material, identity := Sha256.hex bytes : FamilyBindingEvidence }
    return {
      bridgeKind := "family-forward", family := some family, continuation := some { kind := "open" } }
  let (evidence, remaining) ← action.run limit
  return (evidence, limit - remaining)

end LeanInformationAudit.FamilyRegistration
