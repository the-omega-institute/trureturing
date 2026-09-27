import Reg.D5.S3.Arith.Erdos699DenominatorGap

open Lean Meta LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Arith.Erdos699DenominatorGap

namespace LeanInformationAuditRegTests.Erdos699SourceContract

/-- Unexpected exceptions do not count as the intended negative result. -/
private def rejectsExactly (expected : String) (action : MetaM Unit) : MetaM Unit := do
  let failure ← try
    action
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  unless failure == some expected do
    throwError "[FAIL] expected {expected}, received {failure}"
  logInfo m!"[PASS] {expected}"

private def removeBinder : Nat → Expr → Expr
  | 0, .forallE _ _ body _ => body.instantiate1 (mkConst ``True.intro)
  | n + 1, .forallE name domain body bi =>
      .forallE name domain (removeBinder n body) bi
  | _, e => e

run_meta do
  let target := ``D5.S3.Arith.Erdos699DenominatorGap.erdos699_denominator_gap
  let owner := `Reg.D5.S3.Arith.Erdos699DenominatorGap
  let sourceOwner := `D5.S3.Arith.Erdos699DenominatorGap
  let env ← getEnv
  let info ← getConstInfo target
  unless info.isTheorem && RegistrationReifier.declaringModuleOf env target == some sourceOwner do
    throwError "[FAIL] original source theorem/owner"
  let #[event] := (TemplateBinding.inventory env).filter (·.key.theoremName == target)
    | throwError "[FAIL] expected exactly one original Erdos699 occurrence"
  unless event.key.registrationModule == owner do throwError "[FAIL] source owner mirror"
  let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
    | throwError "[FAIL] original source claim missing"
  let record ← TemplateBinding.assess event (some claim)
  let .declaredValidated cert := record.result
    | throwError "[FAIL] source assessment: {(← TemplateBinding.recordJson record).compress}"
  let some binding := cert.sourceBinding | throwError "[FAIL] source binding missing"
  unless record.escape.bridgeKind == "source-equivalence" &&
      record.escape.fromObject.any (·.name == target) &&
      record.escape.continuation.any (·.kind == "open") do
    throwError "[FAIL] incomplete four-slot evidence"
  let .ok (rawIdentity, _) := TemplateAudit.compactRawIdentity info.levelParams info.type
    | throwError "[FAIL] raw source identity"
  unless (binding.getObjValAs? String "source_name") == .ok target.toString &&
      (binding.getObjValAs? String "source_owner") == .ok sourceOwner.toString &&
      (binding.getObjValAs? String "source_type_identity") == .ok rawIdentity &&
      (binding.getObjValAs? Nat "telescope_size") == .ok 15 &&
      (binding.getObjValAs? Nat "level_count") == .ok 0 &&
      (binding.getObjValAs? (Array Nat) "coordinates") == .ok #[] do
    throwError "[FAIL] complete original source identity/telescope"
  let some selection := claim.escapeInput.sourceSelection
    | throwError "[FAIL] source selection missing"
  let (scope, _) ← (SourceScope.resolve info selection).run 524288
  let #[readout] := scope.readouts | throwError "[FAIL] expected exactly one source readout"
  unless scope.telescope.size == 15 && scope.levels.isEmpty && scope.coordinates.isEmpty &&
      scope.readouts.size == 1 && selection.readouts[0]!.stateBinder == 0 &&
      readout.context.size == 15 &&
      (scope.telescope.extract 0 7).map (·.name) == #[`n, `L, `R, `j, `m, `D, `k] do
    throwError "[FAIL] original seven parameters and eight assumptions in order"
  let mut conclusion := info.type
  for _ in [:15] do conclusion := conclusion.bindingBody!
  unless conclusion.isAppOfArity ``LT.lt 4 &&
      readout.observation.equal conclusion.getAppArgs[2]! do
    throwError "[FAIL] source selection must be exactly the original conclusion LHS"
  discard <| (SourceScope.validateFields scope (mkConst ``signature)
    (mkConst ``actual)).run 524288
  let law ← mkAppM ``Arena.Law #[mkConst ``arena, mkConst ``actual]
  discard <| (SourceScope.reconstruct info.type law).run 524288
  logInfo "[PASS] original_LHS_extraction_full_fifteen_binder_Law_reconstruction"
  for ordinal in [7:15] do
    let expected := if ordinal == 14 then "unclassified_form:source.missing_binder"
      else "unclassified_form:source.statement_reconstruction"
    rejectsExactly expected do
      discard <| (SourceScope.reconstruct info.type (removeBinder ordinal info.type)).run 524288
    logInfo m!"[PASS] missing_original_assumption_{ordinal}"
  let weakened ← forallTelescope info.type fun xs body => do
    let args := body.getAppArgs
    mkForallFVars xs (← mkAppM ``LE.le #[args[2]!, args[3]!])
  rejectsExactly "unclassified_form:source.statement_reconstruction" do
    discard <| (SourceScope.reconstruct info.type weakened).run 524288
  logInfo "[PASS] weakened_original_strict_conclusion"
  let .forallE name domain body _ := info.type | throwError "[FAIL] original telescope"
  rejectsExactly "unclassified_form:source.telescope_reconstruction" do
    discard <| (SourceScope.reconstruct info.type (.forallE name domain body .implicit)).run 524288
  rejectsExactly "unclassified_form:source.actual_observation" do
    discard <| (SourceScope.validateFields scope (mkConst ``signature)
      (mkConst ``rejected)).run 524288
  let wrongState := selection.readouts.map (fun r => { r with stateBinder := 1 })
  rejectsExactly "unclassified_form:source.coordinate_dependency" do
    discard <| (SourceScope.resolve info { selection with readouts := wrongState }).run 524288
  let badReadout ← mkAppM ``Realization.readout #[mkConst ``rejected]
  let badAnchor ← mkAppM ``Realization.anchor #[mkConst ``rejected]
  let distorted ← mkAppM ``realize #[mkConst ``signature, badReadout, badAnchor]
  let changed ← TemplateBinding.assess event (some { claim with descriptor := some distorted })
  let .declaredUnresolved diagnostic := changed.result
    | throwError "[FAIL] accepted altered declared readout"
  unless (diagnostic.splitOn "rule=source.descriptor_actual ").length == 2 do
    throwError "[FAIL] unexpected altered-readout diagnostic: {diagnostic}"
  logInfo "[PASS] full_assessment_rejects_altered_descriptor"
  for name in #[target, ``registration, ``rejected_law] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "[FAIL] nonstandard axiom closure: {name}: {axioms}"
    logInfo m!"[PASS] standard_axioms {name}: {axioms}"
  let snapshot ← TemplateBinding.exportSnapshot
  let originals := snapshot.originals.filter (·.occurrence.key.registrationModule == owner)
  unless originals.size == 1 && originals[0]!.occurrence.key == event.key do
    throwError "[FAIL] exported source inventory"
  let wires ← TemplateBinding.reportJson #[(owner, #[event.key])]
  IO.FS.writeFile ((← Repository.root) / ".lake/build/erdos699-source-evidence.json")
    ((Json.arr wires).compress ++ "\n")
  logInfo m!"[PASS] original_Erdos699_declared_validated_four_slots evidence_ref={cert.evidenceRef}"

end LeanInformationAuditRegTests.Erdos699SourceContract
