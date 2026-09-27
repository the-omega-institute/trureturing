import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.TrajectorySourceContract

private def mustReject (label : String) (action : MetaM Unit) : MetaM Unit := do
  let reason ← try action; pure "accepted" catch ex => ex.toMessageData.toString
  unless reason.startsWith "unclassified_form:source." ||
      reason.startsWith "forbidden_dependency:" do
    throwError "unexpected trajectory rejection for {label}: {reason}"
  logInfo m!"[PASS] trajectory_rejects_{label}"

private def replaceAt (source : Expr) (path : List String) (replacement : Expr) : MetaM Expr :=
  match source, path with
  | _, [] => pure replacement
  | .forallE n d b bi, "body" :: rest =>
    return .forallE n d (← replaceAt b rest replacement) bi
  | .forallE n d b bi, "domain" :: rest =>
    return .forallE n (← replaceAt d rest replacement) b bi
  | .lam n d b bi, "body" :: rest =>
    return .lam n d (← replaceAt b rest replacement) bi
  | .app f a, "fn" :: rest => return .app (← replaceAt f rest replacement) a
  | .app f a, "arg" :: rest => return .app f (← replaceAt a rest replacement)
  | _, _ => throwError "regression mutation path is absent"

run_meta do
  let cases := #[
    (`D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory,
      `has_law_traj_measure, 14, #[0, 3, 10], 14, #[1, 4, 6, 8, 9, 11, 12, 13]),
    (`D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass,
      `markov_chain_law_map_prefix_apply_singleton, 9, #[0, 7], 9, #[1, 4, 5, 6])]
  let mut selection := #[]
  for (owner, shortName, telescope, coordinates, state, fixedBinders) in cases do
    let name := owner ++ shortName
    let env ← getEnv
    let #[event] := (TemplateBinding.inventory env).filter (·.key.theoremName == name)
      | throwError "expected one original trajectory registration"
    unless event.key.registrationModule == `Reg ++ owner do throwError "wrong source mirror"
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "original trajectory claim absent"
    let before := (TemplateBinding.observedAssessments env).size
    let record ← TemplateBinding.assess event (some claim)
    unless (TemplateBinding.observedAssessments (← getEnv)).size == before + 1 do
      throwError "trajectory evidence used a cached assessment"
    let .declaredValidated cert := record.result
      | throwError "trajectory source failed: {(← TemplateBinding.recordJson record).compress}"
    unless cert.sourceBinding.isSome && record.escape.fromObject.isSome &&
        record.escape.bridgeKind == "source-equivalence" &&
        record.escape.continuation.any (·.kind == "open") do throwError "incomplete four slots"
    let some source := claim.escapeInput.sourceSelection | throwError "missing source selection"
    let info ← getConstInfo name
    let (scope, _) ← (SourceScope.resolve info source).run 524288
    let #[readout] := scope.readouts | throwError "expected the complete path readout"
    unless scope.telescope.size == telescope && source.coordinates == coordinates &&
        source.readouts[0]!.stateBinder == state && readout.context.size == state + 1 &&
        readout.context[state]!.isLambda do throwError "trajectory source scope changed"
    let levels := info.levelParams.map Level.param
    mustReject "wrong_owner" do
      discard <| (SourceScope.resolve info { source with owner := `D5.Other }).run 524288
    mustReject "absent_path" do
      discard <| (SourceScope.resolve info { source with readouts :=
        #[{ path := #["invalid"], stateBinder := state }] }).run 524288
    let outside := source.readouts.map (fun r => { r with stateBinder := state + 1 })
    mustReject "out_of_scope_state" do
      discard <| (SourceScope.resolve info { source with readouts := outside }).run 524288
    for binder in fixedBinders do
      mustReject s!"fixed_premise_as_coordinate_{binder}" do
        discard <| (SourceScope.resolve info { source with coordinates := #[binder] }).run 524288
    mustReject "erased_trajectory" do
      discard <| (SourceScope.validateFields scope
        (mkConst (`Reg ++ owner ++ `signature) levels)
        (mkConst (`Reg ++ owner ++ `rejected) levels)).run 524288
    mustReject "dropped_original_telescope" do
      discard <| (SourceScope.reconstruct info.type (mkConst ``True)).run 524288
    for binder in fixedBinders do
      let weakened ← replaceAt info.type (List.replicate binder "body" ++ ["domain"])
        (mkConst ``True)
      mustReject s!"dropped_probability_kernel_or_process_premise_{binder}" do
        discard <| (SourceScope.reconstruct info.type weakened).run 524288
    for operand in #[mkConst name levels, info.type,
        mkApp (.lam `P (mkSort .zero) (mkConst ``Unit.unit) .default) info.type,
        mkApp (mkConst ``Decidable) info.type] do
      mustReject "theorem_answer_proof_or_dead_argument" do
        discard <| SourceOperands.check name #[operand] 524288
    selection := selection.push (event.key.registrationModule, #[event.key])
    logInfo m!"[PASS] {name} evidence_ref={cert.evidenceRef}"
  IO.FS.writeFile ((← Repository.root) / ".lake/build/trajectory-source-evidence.json")
    ((Json.arr (← TemplateBinding.reportJson selection)).compress ++ "\n")

end LeanInformationAuditRegTests.TrajectorySourceContract
