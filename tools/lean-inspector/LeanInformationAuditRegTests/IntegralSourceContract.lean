import Reg.D5.S3.Weil.Mertens.Gamma
import Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition

open Lean Meta LeanInformationAudit
open MeasureTheory Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace LeanInformationAuditRegTests.IntegralSourceContract

private def mustReject (label : String) (action : MetaM Unit) : MetaM Unit := do
  let rejected ← try action; pure false catch _ => pure true
  unless rejected do throwError "accepted invalid integral evidence: {label}"
  logInfo m!"[PASS] integral_rejects_{label}"

-- Dropping the positivity premise changes the actual source statement.
def unguardedArchimedean : Prop := ∀ {c t : ℝ},
  (∫ x in Ioi (0 : ℝ), Real.exp (-c * x) * Real.cos (t * x)) =
    c / (c ^ 2 + t ^ 2)

example : ¬ ObservationalDependence
    Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.signature
    Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.rejected := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  exact hxy rfl

run_meta do
  let cases := #[
    (``integral_log_mul_exp_neg_eq_deriv_Gamma, `D5.S3.Weil.Mertens.Gamma,
      ``Reg.D5.S3.Weil.Mertens.Gamma.signature,
      ``Reg.D5.S3.Weil.Mertens.Gamma.rejected, 0, 0),
    (``D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.integral_exp_neg_mul_cos,
      `D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition,
      ``Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.signature,
      ``Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.rejected, 3, 3)]
  let mut selection := #[]
  for (name, owner, signature, rejected, telescope, state) in cases do
    let env ← getEnv
    unless RegistrationReifier.declaringModuleOf env name == some owner do
      throwError "wrong original compiler owner: {name}"
    let #[event] := (TemplateBinding.inventory env).filter (·.key.theoremName == name)
      | throwError "expected one original integral registration: {name}"
    unless event.key.registrationModule == `Reg ++ owner do throwError "wrong source mirror"
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "original integral claim absent"
    let before := (TemplateBinding.observedAssessments env).size
    let record ← TemplateBinding.assess event (some claim)
    unless (TemplateBinding.observedAssessments (← getEnv)).size == before + 1 do
      throwError "integral evidence used a cached assessment"
    let .declaredValidated cert := record.result
      | throwError "integral source failed: {(← TemplateBinding.recordJson record).compress}"
    unless cert.sourceBinding.isSome && record.escape.fromObject.isSome &&
        record.escape.bridgeKind == "source-equivalence" &&
        record.escape.continuation.any (·.kind == "open") do throwError "incomplete four slots"
    let some source := claim.escapeInput.sourceSelection | throwError "missing source selection"
    let info ← getConstInfo name
    let (scope, _) ← (SourceScope.resolve info source).run 524288
    let #[readout] := scope.readouts | throwError "expected one integrand"
    unless scope.telescope.size == telescope &&
        readout.context.size == state + 1 && source.readouts[0]!.stateBinder == state &&
        readout.context[state]!.isLambda do
      throwError "integral state is not its actual lambda-bound real variable"
    let expectedCoordinates := if telescope == 0 then #[] else #[0, 1]
    unless source.coordinates == expectedCoordinates do throwError "source parameters changed"
    logInfo m!"[PASS] original_integral {name} evidence_ref={cert.evidenceRef}"
    selection := selection.push (event.key.registrationModule, #[event.key])
    mustReject "wrong_owner" do
      discard <| (SourceScope.resolve info { source with owner := `D5.Other }).run 524288
    mustReject "absent_path" do
      discard <| (SourceScope.resolve info { source with readouts :=
        #[{ path := #["invalid"], stateBinder := state }] }).run 524288
    let outside := source.readouts.map (fun r => { r with stateBinder := state + 1 })
    mustReject "state_outside_integrand" do
      discard <| (SourceScope.resolve info { source with readouts := outside }).run 524288
    mustReject "substituted_integrand" do
      discard <| (SourceScope.validateFields scope
        (mkConst signature) (mkConst rejected)).run 524288
    let expected ← mkAppM ``Sensitivity #[mkConst event.key.objectArena,
      ← mkAppM ``Registration.actual #[mkConst event.realizationName]]
    unless !(← RegistrationGates.checked ``True.intro expected) do
      throwError "unrelated sensitivity proof accepted"
    if telescope == 3 then
      mustReject "positivity_as_variable" do
        discard <| (SourceScope.resolve info { source with coordinates := #[0, 1, 2] }).run 524288
      mustReject "dropped_positivity" do
        discard <| (SourceScope.reconstruct info.type (mkConst ``unguardedArchimedean)).run 524288
      let .forallE n d b _ := info.type | throwError "outer parameter missing"
      mustReject "explicit_instead_of_implicit_parameter" do
        discard <| (SourceScope.reconstruct info.type (.forallE n d b .default)).run 524288
  let wire := Json.arr (← TemplateBinding.reportJson selection)
  IO.FS.writeFile ((← Repository.root) / ".lake/build/integral-source-evidence.json")
    (wire.compress ++ "\n")
  logInfo "[PASS] two_original_integrals_current_production_export"

end LeanInformationAuditRegTests.IntegralSourceContract
