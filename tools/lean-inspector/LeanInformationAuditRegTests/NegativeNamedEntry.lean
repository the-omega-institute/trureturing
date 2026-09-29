import Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.NegativeNamedEntry

private partial def changeDomain (index : Nat) : Expr → Expr
  | .forallE n d b bi => if index == 0 then .forallE n (mkConst ``True) b bi
    else .forallE n d (changeDomain (index - 1) b) bi
  | e => e

private partial def changeBinder (index : Nat) : Expr → Expr
  | .forallE n d b bi => if index == 0 then
      .forallE n d b (if bi == .default then .implicit else .default)
    else .forallE n d (changeBinder (index - 1) b) bi
  | e => e

private def mustReject (rule : String) (action : MetaM Unit) : MetaM Unit := do
  let result ← try action; pure "accepted" catch e => e.toMessageData.toString
  unless result.contains rule do throwError "expected {rule}, got {result}"
  logInfo m!"[PASS] original negative source rejects {rule}"

run_meta do
  let target := ``D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.result
  let env ← getEnv
  let some event := (TemplateBinding.inventory env).find? (·.key.theoremName == target)
    | throwError "original negative occurrence absent"
  let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
    | throwError "original negative claim absent"
  let record ← TemplateBinding.assess event (some claim)
  let .declaredValidated _ := record.result
    | throwError "negative source failed: {(← TemplateBinding.recordJson record).compress}"
  let some selection := claim.escapeInput.sourceSelection | throwError "selection missing"
  let info ← getConstInfo target
  let (scope, _) ← (SourceScope.resolve info selection).run 524288
  let some definition := scope.definition | throwError "definition missing"
  unless scope.source.equal info.type && scope.expanded.isAppOfArity ``Not 1 &&
      scope.expanded.getAppArgs[0]!.equal definition.value && definition.path == #["arg"] do
    throwError "lost the original negative statement"
  let some selected := selection.definition | throwError "selection missing"
  mustReject "source.definition_reference" do
    discard <| (SourceScope.resolve info { selection with
      definition := some { selected with path := #[] } }).run 524288
  for path in #[#["fn"], #["arg", "arg"], #["body"], #["normalize"]] do
    mustReject "source.definition_path" do
      discard <| (SourceScope.resolve info { selection with
        definition := some { selected with path } }).run 524288
  mustReject "source.absent_occurrence" do
    discard <| (SourceScope.resolve info { selection with definition := none }).run 524288
  mustReject "source.definition_readout_path" do
    discard <| (SourceScope.resolve info { selection with
      readouts := #[{ path := #["fn", "arg"], stateBinder := 0 }] }).run 524288
  mustReject "source.duplicate_occurrence" do
    discard <| (SourceScope.resolve info { selection with
      readouts := selection.readouts ++ selection.readouts }).run 524288
  mustReject "source.dictionary_or_proof_coordinate" do
    discard <| (SourceScope.resolve info { selection with coordinates := #[1,2] }).run 524288
  for changed in #[definition.value, mkApp (mkConst ``Not) (mkApp (mkConst ``Not) definition.value),
      mkConst ``True, mkConst ``False] do
    mustReject "unclassified_form:source." do
      discard <| (SourceScope.reconstruct scope.expanded changed).run 524288
  let .forallE n d b _ := definition.value | throwError "dimension binder absent"
  mustReject "source.telescope_reconstruction" do
    discard <| (SourceScope.reconstruct scope.expanded
      (mkApp (mkConst ``Not) (.forallE n d b .implicit))).run 524288
  -- Every dimension/group/dictionary/operator/subspace/hypothesis/conjugation binder remains.
  for index in Array.range 12 do
    mustReject "source.telescope_reconstruction" do
      discard <| (SourceScope.reconstruct scope.expanded
        (mkApp (mkConst ``Not) (changeBinder index definition.value))).run 524288
    -- The operator's domain is itself a function telescope; deleting it has
    -- the existing precise missing-binder diagnostic.
    let rule := if index == 4 then "source.missing_binder" else "source.statement_reconstruction"
    mustReject rule do
      discard <| (SourceScope.reconstruct scope.expanded
        (mkApp (mkConst ``Not) (changeDomain index definition.value))).run 524288
  mustReject "source.actual_observation" do
    discard <| (SourceScope.validateFields scope
      (mkConst ``Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.signature)
      (mkConst ``Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.rejected)).run 524288
  mustReject "source.operand_identity" do
    discard <| SourceOperands.check target #[mkConst target] 524288 none (some definition.value)
  let decision ← mkAppM ``Classical.propDecidable #[info.type]
  -- Direct decidability extraction reaches the existing unlinked choice guard.
  mustReject "source.unlinked_operand:Classical.choice" do
    discard <| SourceOperands.check target #[decision] 524288 none (some definition.value)
  for name in #[target, event.realizationName] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "nonstandard axiom closure"
    logInfo m!"NEGATIVE_NAMED_AXIOMS {name}: {axioms}"
  logInfo "[PASS] original full negative named client declared_validated"

end LeanInformationAuditRegTests.NegativeNamedEntry
