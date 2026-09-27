import Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn

open Lean Meta LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.SolidPartitionFirstColumn
open Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn

namespace LeanInformationAuditRegTests.SolidPartitionSourceContract

private def expectedSource : Prop :=
  ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → firstColumn d n = tau d n ∧
    shrinkColumn d n = tau d (n + 1)

private def expectedLaw (r : Realization signature) : Prop :=
  ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → firstColumn d n = r.readout () d n ∧
    shrinkColumn d n = tau d (n + 1)

private def withoutDimensionGuard : Prop :=
  ∀ d n : ℕ, 1 ≤ n → firstColumn d n = tau d n ∧ shrinkColumn d n = tau d (n + 1)

private def withoutSizeGuard : Prop :=
  ∀ d n : ℕ, 1 ≤ d → firstColumn d n = tau d n ∧ shrinkColumn d n = tau d (n + 1)

private def withoutSecondConjunct : Prop :=
  ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → firstColumn d n = tau d n

private def removeBinder : Nat → Expr → Expr
  | 0, .forallE _ _ body _ => body.instantiate1 (mkConst ``True.intro)
  | n + 1, .forallE name domain body bi => .forallE name domain (removeBinder n body) bi
  | _, e => e

private def dropSecond : Expr → Expr
  | .forallE n d b bi => .forallE n d (dropSecond b) bi
  | e => if e.isAppOfArity ``And 2 then e.getAppArgs[0]! else e

private def mustReject (rule : String) (action : MetaM Unit) : MetaM Unit := do
  let failure ← try action; pure none catch e => pure (some (← e.toMessageData.toString))
  unless failure == some ("unclassified_form:" ++ rule) do
    throwError "expected exact {rule}, got {failure}"
  logInfo m!"[PASS] {rule}"

private def verifiedMutation (original changed : Expr) (expectedName : Name)
    (rule : String) : MetaM Unit := do
  let some expectedExpr := (← getConstInfo expectedName).value?
    | throwError "missing expected mutation"
  checkWithKernel changed
  unless changed.equal expectedExpr do
    throwError "mutation does not match its independent expectedExpr: {expectedName}"
  logInfo m!"[PASS] expectedExpr {expectedName}"
  mustReject rule do
    discard <| (SourceScope.reconstruct original changed).run 524288

run_meta do
  let owner := `D5.S3.Combinatorics.SolidPartitionFirstColumn
  let target := owner ++ `result
  let env ← getEnv
  let #[event] := (TemplateBinding.inventory env).filter (·.key.theoremName == target)
    | throwError "expected exactly one original occurrence"
  let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
    | throwError "missing source claim"
  let record ← TemplateBinding.assess event (some claim)
  let .declaredValidated cert := record.result
    | throwError "registration rejected: {(← TemplateBinding.recordJson record).compress}"
  unless record.escape.fromObject.any (·.name == target) &&
      record.escape.bridgeKind == "source-equivalence" &&
      record.escape.continuation.any (·.kind == "open") do throwError "incomplete four slots"
  let some selection := claim.escapeInput.sourceSelection | throwError "missing source selection"
  let info ← getConstInfo target
  let (scope, _) ← (SourceScope.resolve info selection).run 524288
  let some definition := scope.definition | throwError "missing original named entry"
  let #[readout] := scope.readouts | throwError "expected one original tau readout"
  unless definition.name == owner ++ `claim && info.type.equal (mkConst (owner ++ `claim)) &&
      scope.source.equal info.type && scope.expanded.equal definition.value &&
      scope.telescope.isEmpty && scope.levels.isEmpty && selection.coordinates == #[0] &&
      selection.readouts.size == 1 && selection.readouts[0]!.stateBinder == 1 &&
      readout.context.size == 4 do
    throwError "wrong exact source, dimension coordinate, size state or full telescope"
  -- The raw theorem type is the closed named claim; its four binders are in the readout scope.
  let some expected := (← getConstInfo ``expectedSource).value?
    | throwError "missing expected source"
  unless definition.value.equal expected do
    throwError "full original all-dimensions statement changed"
  discard <| (SourceScope.validateFields scope (mkConst ``signature) (mkConst ``actual)).run 524288
  let law ← mkAppM ``Arena.Law #[mkConst ``arena, mkConst ``actual]
  discard <| (SourceScope.reconstruct definition.value law).run 524288
  -- Check all realizations, not merely the law at the proved actual realization.
  withLocalDeclD `r (← mkAppM ``Realization #[mkConst ``signature]) fun r => do
    let expected ← whnf (mkApp (mkConst ``expectedLaw) r)
    let law ← mkAppM ``Arena.Law #[mkConst ``arena, r]
    discard <| (SourceScope.reconstruct expected law).run 524288
  unless ← isDefEq (← mkAppM ``Signature.Params #[mkConst ``signature]) (mkConst ``Nat) do
    throwError "dimension zero was excluded from the signature"
  logInfo "[PASS] full original and arbitrary-realization Law; unrestricted dimension includes zero"
  mustReject "source.absent_occurrence" do
    discard <| (SourceScope.resolve info { selection with definition := none }).run 524288
  mustReject "source.dictionary_or_proof_coordinate" do
    discard <| (SourceScope.resolve info { selection with coordinates := #[0, 2] }).run 524288
  mustReject "source.actual_observation" do
    discard <| (SourceScope.validateFields scope
      (mkConst ``signature) (mkConst ``rejected)).run 524288
  verifiedMutation definition.value (removeBinder 2 definition.value)
    ``withoutDimensionGuard "source.statement_reconstruction"
  verifiedMutation definition.value (removeBinder 3 definition.value)
    ``withoutSizeGuard "source.missing_binder"
  verifiedMutation definition.value (dropSecond definition.value)
    ``withoutSecondConjunct "source.statement_reconstruction"
  for name in #[target, event.realizationName, ``rejected_law, ``dependence_proof] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "nonstandard axiom closure"
    logInfo m!"[PASS] standard axioms {name}: {axioms}"
  logInfo m!"[PASS] complete original SolidPartition source and four-slot contract: \
    {cert.evidenceRef}"

end LeanInformationAuditRegTests.SolidPartitionSourceContract
