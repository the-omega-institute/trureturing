import Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation

open Lean Meta LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace LeanInformationAuditRegTests.PrimitiveBridgeSourceContract

private def mustReject (rule : String) (action : MetaM Unit) : MetaM Unit := do
  let result ← try action; pure "accepted" catch e => e.toMessageData.toString
  unless result.contains rule do throwError "expected {rule}, got {result}"
  logInfo m!"[PASS] primitive_bridge_rejects {rule}"

example : ¬ ObservationalDependence
    Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.signature
    Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.rejected := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  exact hxy rfl

private partial def dropAnnihilator (e : Expr) : Expr :=
  if e.isAppOfArity ``Iff 2 then e.getAppArgs[0]!
  else match e with
    | .app f a => .app (dropAnnihilator f) (dropAnnihilator a)
    | .lam n d b bi => .lam n d (dropAnnihilator b) bi
    | .forallE n d b bi => .forallE n d (dropAnnihilator b) bi
    | .letE n d v b nd => .letE n d v (dropAnnihilator b) nd
    | _ => e

run_meta do
  let name := ``D5.S3.TotalVariation.PrimitiveBridgeCancellation.primitive_bridge_cancellation
  let env ← getEnv
  let #[event] := (TemplateBinding.inventory env).filter (·.key.theoremName == name)
    | throwError "expected one bridge original registration"
  let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
    | throwError "missing original claim"
  let before := (TemplateBinding.observedAssessments env).size
  let record ← TemplateBinding.assess event (some claim)
  unless (TemplateBinding.observedAssessments (← getEnv)).size == before + 1 do
    throwError "assessment was not recomputed"
  let .declaredValidated cert := record.result
    | throwError "bridge source failed: {(← TemplateBinding.recordJson record).compress}"
  unless cert.sourceBinding.isSome && record.escape.fromObject.isSome &&
      record.escape.bridgeKind == "source-equivalence" &&
      record.escape.continuation.any (·.kind == "open") do throwError "incomplete four slots"
  let some selection := claim.escapeInput.sourceSelection | throwError "missing selection"
  let info ← getConstInfo name
  let (scope, _) ← (SourceScope.resolve info selection).run 524288
  let #[readout] := scope.readouts | throwError "expected one readout"
  unless scope.telescope.size == 11 && scope.readouts.size == 1 &&
      readout.context.size == 15 && selection.coordinates == #[7,12] &&
      selection.readouts[0]!.stateBinder == 14 do throwError "original scope changed"
  mustReject "source.dictionary_or_proof_coordinate" do
    discard <| (SourceScope.resolve info { selection with coordinates := #[0,1,7,12] }).run 524288
  mustReject "source.coordinate_dependency" do
    discard <| (SourceScope.resolve info { selection with coordinates := #[12] }).run 524288
  mustReject "source.owner" do
    discard <| (SourceScope.resolve info { selection with owner := `D5.Other }).run 524288
  mustReject "source.state_binder" do
    discard <| (SourceScope.resolve info { selection with readouts :=
      (selection.readouts.map (fun r => { r with stateBinder := 15 })) }).run 524288
  mustReject "source.statement_reconstruction" do
    discard <| (SourceScope.reconstruct info.type (dropAnnihilator info.type)).run 524288
  let levels := info.levelParams.map Level.param
  mustReject "source.actual_observation" do
    discard <| (SourceScope.validateFields scope
      (mkConst ``Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.signature)
      (mkConst ``Reg.D5.S3.TotalVariation.PrimitiveBridgeCancellation.rejected)).run 524288
  let .forallE n d b bi := info.type | throwError "vertex type binder missing"
  mustReject "source.telescope_reconstruction" do
    discard <| (SourceScope.reconstruct info.type (.forallE n d b
      (if bi == .default then .implicit else .default))).run 524288
  let expected ← mkAppM ``Sensitivity #[mkConst event.key.objectArena levels,
    ← mkAppM ``Registration.actual #[mkConst event.realizationName levels]]
  unless !(← RegistrationGates.checked ``True.intro expected) do
    throwError "unrelated sensitivity proof accepted"
  logInfo m!"[PASS] original_primitive_bridge_four_slots evidence_ref={cert.evidenceRef}"

end LeanInformationAuditRegTests.PrimitiveBridgeSourceContract
