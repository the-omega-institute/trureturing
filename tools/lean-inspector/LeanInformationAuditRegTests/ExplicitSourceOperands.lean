import Reg.Support.DependentFamily
import Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.ExplicitSourceOperands

def readout (n : Nat) := n
def predicate (n : Nat) : Prop := n = 0
instance (n : Nat) : Decidable (predicate n) := inferInstanceAs (Decidable (n = 0))
theorem injective : Function.Injective readout := fun _ _ h => h
theorem admitted : predicate 0 ∧ True := ⟨rfl, True.intro⟩
def dependent (n : Nat) : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
def typeInput (_ : Type) : Nat := 0
def proofInput (_ : True) : Nat := 0
theorem dependentUse : dependent 0 = dependent 0 := rfl
theorem typeUse : typeInput Nat = 0 := rfl
theorem proofUse : proofInput True.intro = 0 := rfl

private def rejects (rule : String) (action : SourceScope.M Unit) : MetaM Unit := do
  let result ← try discard <| action.run 524288; pure "accepted"
    catch error => error.toMessageData.toString
  unless result.contains rule do throwError "expected {rule}, got {result}"

run_meta do
  let info ← getConstInfo ``injective
  let selection : SourceSelection := {
    owner := `LeanInformationAuditRegTests.ExplicitSourceOperands
    coordinates := #[]
    readouts := #[{path := #["arg"], functionOperand := true}] }
  let (scope, _) ← (SourceScope.resolve info selection).run 524288
  let some first := scope.readouts[0]? | throwError "missing readout"
  unless scope.readouts.size == 1 && first.rawContext.isEmpty do
    throwError "function source lost original empty scope"
  let ((_, observation), _) ← (SourceScope.atPath info.type #["arg"]).run 524288
  unless first.rawObservation.equal observation do
    throwError "function source lost exact original operand"
  rejects "source.operand_mode" <| discard <| SourceScope.resolve info
    {selection with readouts := #[{path := #["arg"], functionOperand := true, stateBinder := 1}]}
  rejects "source.function_operand" <| discard <| SourceScope.resolve info
    {selection with readouts := #[{path := #[], functionOperand := true}]}
  rejects "source.owner" <| discard <| SourceScope.resolve info {selection with owner := `Wrong}
  for name in #[``dependentUse, ``typeUse, ``proofUse] do
    rejects "source.function_operand" <| discard <| SourceScope.resolve (← getConstInfo name)
      {selection with readouts := #[{path := #["fn", "arg", "fn"], functionOperand := true}]}
  let info ← getConstInfo ``admitted
  let selection : SourceSelection := {
    owner := selection.owner
    coordinates := #[]
    readouts := #[{path := #["fn", "arg"], stateOperand := some #["arg"], booleanPredicate := true}] }
  let (scope, _) ← (SourceScope.resolve info selection).run 524288
  let predicate := mkApp (mkConst ``predicate) (mkNatLit 0)
  let expected := mkApp2 (mkConst ``And) (← mkEq (← mkDecide predicate) (mkConst ``Bool.true)) (mkConst ``True)
  discard <| (SourceScope.reconstruct scope.expanded expected).run 524288
  rejects "source.statement_reconstruction" <| SourceScope.reconstruct scope.expanded (mkConst ``False)
  rejects "source.state_operand_path" <| discard <| SourceScope.resolve info
    {selection with readouts := #[{path := #["fn", "arg"], stateOperand := some #[], booleanPredicate := true}]}
  rejects "source.observation_data" <| discard <| SourceScope.resolve info
    {selection with readouts := #[{path := #["fn", "arg"], stateOperand := some #["arg"]}]}
  logInfo "[PASS] exact function and Boolean predicate operands; nine rejection boundaries"

end LeanInformationAuditRegTests.ExplicitSourceOperands

namespace LeanInformationAuditRegTests.ExplicitSourceOperands
open Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep

run_meta do
  let info ← getConstInfo ``D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.incoming_response_matrix_factor_step
  let path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
  let selection : SourceSelection := {
    owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := path
      stateOperand := some #["fn"]
      stateBinder := 0
      functionOperand := false
      booleanPredicate := false}] }
  logInfo "[START] resolve"
  let (scope, fuel) ← (SourceScope.resolve info selection).run 524288
  logInfo m!"[PASS] resolve work={524288-fuel}"
  unless scope.source.equal info.type && scope.expanded.equal info.type &&
      scope.levels == info.levelParams && scope.levels.isEmpty && scope.telescope.size == 7 do
    throwError "source identity/universes/telescope changed"
  unless scope.telescope.map (·.info) ==
      #[.implicit, .implicit, .implicit, .default, .default, .instImplicit, .instImplicit] do
    throwError "binder modes changed"
  let ((context, raw), _) ← (SourceScope.atPath info.type path).run 524288
  let some readout := scope.readouts[0]? | throwError "missing readout"
  unless readout.rawObservation.equal raw && readout.rawContext.size == context.size do
    throwError "raw observation changed"
  logInfo m!"[PASS] original={info.name} levels={info.levelParams} telescope={scope.telescope.map (·.name)}"
  logInfo "[START] validateFields"
  discard <| (SourceScope.validateFields scope (mkConst ``signature) (mkConst ``actual)).run 524288
  logInfo "[PASS] inferred dependent family state and whole matrix output; actual evaluation"
  logInfo "[START] reconstruct"
  let law ← mkAppM ``D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law #[mkConst ``arena, mkConst ``actual]
  discard <| (SourceScope.reconstruct scope.expanded law).run 524288
  logInfo "[PASS] full law reconstruction"
  rejects "source.function_operand" <| discard <| SourceScope.resolve info
    {selection with readouts := #[{path := path.push "fn", functionOperand := true}]}
  rejects "source.state_operand_path" <| discard <| SourceScope.resolve info
    {selection with readouts := #[{path, stateOperand := some #[]}]}
  rejects "source.coordinate_dependency" <| discard <| SourceScope.resolve info
    {selection with readouts := #[{path, stateOperand := some #["arg"]}]}
  for i in #[5, 6] do
    rejects "source.dictionary_or_proof_coordinate" <| discard <| SourceScope.resolve info
      {selection with coordinates := selection.coordinates.push i}
  let .forallE name domain body _ := info.type | throwError "missing first binder"
  rejects "source.telescope_reconstruction" <| SourceScope.reconstruct info.type
    (.forallE name domain body .default)
  rejects "source.missing_binder" <| SourceScope.reconstruct info.type (mkConst ``True)

  rejects "source.actual_observation" <| discard <| SourceScope.validateFields scope
    (mkConst ``signature) (mkConst ``bad)
  -- A well-typed reflexive equality keeps the telescope but drops the full Law.
  let reflexive ← forallTelescope info.type fun locals conclusion => do
    unless conclusion.isAppOfArity ``Eq 3 do throwError "expected matrix equality"
    mkForallFVars locals (← mkEq conclusion.getAppArgs[1]! conclusion.getAppArgs[1]!)
  checkWithKernel reflexive
  rejects "source.statement_reconstruction" <| SourceScope.reconstruct info.type reflexive
  let env ← getEnv
  let some event := (TemplateBinding.inventory env).find?
      (·.key.theoremName == info.name) | throwError "missing matrix factor occurrence"
  let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
    | throwError "missing matrix factor claim"
  let record ← TemplateBinding.assess event (some claim)
  let .declaredValidated certificate := record.result
    | throwError "matrix factor assessment: {(← TemplateBinding.recordJson record).compress}"
  unless certificate.sourceBinding.isSome && record.escape.bridgeKind == "source-equivalence" &&
      record.escape.fromObject.isSome && record.escape.continuation.any (·.kind == "open") do
    throwError "matrix factor four slots incomplete"
  let badReadout ← mkAppM
    ``D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout #[mkConst ``bad]
  let badAnchor ← mkAppM
    ``D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.anchor #[mkConst ``bad]
  let descriptor ← mkAppM ``D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize
    #[mkConst ``signature, badReadout, badAnchor]
  let changed ← TemplateBinding.assess event (some {claim with descriptor := some descriptor})
  let .declaredUnresolved diagnostic := changed.result
    | throwError "wrong evaluation descriptor accepted"
  unless diagnostic.contains "source.descriptor_actual" do
    throwError "unexpected wrong evaluation refusal: {diagnostic}"
  let discarded := mkApp (.lam `ignored (mkSort .zero) (mkConst ``Unit.unit) .default) info.type
  let proof := Expr.letE `proof info.type (mkConst info.name) (mkConst ``Unit.unit) false
  for operand in #[discarded, proof] do
    let diagnostic ← try
      discard <| SourceOperands.check info.name #[operand] 524288
      pure "accepted"
    catch error => error.toMessageData.toString
    unless diagnostic.contains "forbidden_dependency:source.operand_identity" do
      throwError "raw target operand not refused: {diagnostic}"
  logInfo m!"[PASS] matrix_factor_full_four_slots evidence_ref={certificate.evidenceRef}"

end LeanInformationAuditRegTests.ExplicitSourceOperands
