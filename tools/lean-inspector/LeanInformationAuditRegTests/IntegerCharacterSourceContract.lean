import Reg.D5.S3.Fourier.IntegerCharacterCoercivity

open Lean Meta LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace LeanInformationAuditRegTests.IntegerCharacterSourceContract

private def mustReject (rule : String) (action : MetaM Unit) : MetaM Unit := do
  let result ← try action; pure "accepted" catch e => e.toMessageData.toString
  unless result.contains rule do throwError "expected {rule}, got {result}"
  logInfo m!"[PASS] integer_character_rejects {rule}"

example : ¬ ObservationalDependence
    Reg.D5.S3.Fourier.IntegerCharacterCoercivity.signature.{0}
    Reg.D5.S3.Fourier.IntegerCharacterCoercivity.rejected := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  exact hxy rfl

run_meta do
  let name := ``D5.S3.Fourier.IntegerCharacterCoercivity.integer_character_global_coercivity
  let env ← getEnv
  let #[event] := (TemplateBinding.inventory env).filter (·.key.theoremName == name)
    | throwError "expected one coercivity original registration"
  let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
    | throwError "missing original claim"
  let before := (TemplateBinding.observedAssessments env).size
  let record ← TemplateBinding.assess event (some claim)
  unless (TemplateBinding.observedAssessments (← getEnv)).size == before + 1 do
    throwError "assessment was not recomputed"
  let .declaredValidated cert := record.result
    | throwError "coercivity source failed: {(← TemplateBinding.recordJson record).compress}"
  unless cert.sourceBinding.isSome && record.escape.fromObject.isSome &&
      record.escape.bridgeKind == "source-equivalence" &&
      record.escape.continuation.any (·.kind == "open") do throwError "incomplete four slots"
  let some selection := claim.escapeInput.sourceSelection | throwError "missing selection"
  let info ← getConstInfo name
  let (scope, _) ← (SourceScope.resolve info selection).run 524288
  let #[readout] := scope.readouts | throwError "expected one readout"
  unless scope.telescope.size == 4 && scope.readouts.size == 1 &&
      readout.context.size == 6 && selection.coordinates == #[0,1,3] &&
      selection.readouts[0]!.stateBinder == 5 do throwError "original scope changed"
  mustReject "source.dictionary_or_proof_coordinate" do
    discard <| (SourceScope.resolve info { selection with coordinates := #[0,1,2,3] }).run 524288
  mustReject "source.coordinate_dependency" do
    discard <| (SourceScope.resolve info { selection with coordinates := #[0,3] }).run 524288
  mustReject "source.owner" do
    discard <| (SourceScope.resolve info { selection with owner := `D5.Other }).run 524288
  mustReject "source.state_binder" do
    discard <| (SourceScope.resolve info { selection with readouts :=
      (selection.readouts.map (fun r => { r with stateBinder := 6 })) }).run 524288
  let levels := info.levelParams.map Level.param
  mustReject "source.actual_observation" do
    discard <| (SourceScope.validateFields scope
      (mkConst ``Reg.D5.S3.Fourier.IntegerCharacterCoercivity.signature levels)
      (mkConst ``Reg.D5.S3.Fourier.IntegerCharacterCoercivity.rejected levels)).run 524288
  let .forallE n d b bi := info.type | throwError "dimension binder missing"
  mustReject "source.telescope_reconstruction" do
    discard <| (SourceScope.reconstruct info.type (.forallE n d b
      (if bi == .default then .implicit else .default))).run 524288
  let expected ← mkAppM ``Sensitivity #[mkConst event.key.objectArena levels,
    ← mkAppM ``Registration.actual #[mkConst event.realizationName levels]]
  unless !(← RegistrationGates.checked ``True.intro expected) do
    throwError "unrelated sensitivity proof accepted"
  logInfo m!"[PASS] original_integer_character_four_slots evidence_ref={cert.evidenceRef}"

end LeanInformationAuditRegTests.IntegerCharacterSourceContract
