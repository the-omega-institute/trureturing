import Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound
import Reg.D5.S3.Quantum.Information.FixedSupportFisherGap

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.PhaseFisherSourceContract

private def mustReject (label : String) (action : MetaM Unit) : MetaM Unit := do
  let reason ← try action; pure "accepted" catch ex => ex.toMessageData.toString
  unless reason.startsWith "unclassified_form:source." ||
      reason.startsWith "forbidden_dependency:" do
    throwError "unexpected quantum rejection for {label}: {reason}"
  logInfo m!"[PASS] quantum_rejects_{label}"

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
    (`D5.S3.Quantum.Entanglement.PhaseHistoryBound,
      `actual_source_moments, `Moments, 4, #[0], 3, 9, #[1, 2]),
    (`D5.S3.Quantum.Entanglement.PhaseHistoryBound,
      `phase_history_bound, `Bound, 8, #[0, 3], 6, 8, #[1, 2, 7]),
    (`D5.S3.Quantum.Information.FixedSupportFisherGap,
      `result, Name.anonymous, 15, #[0, 5], 16, 17, #[1, 6, 7, 8, 9, 10, 11, 12, 13])]
  let mut selection := #[]
  for (owner, shortName, part, telescope, coordinates, state, scopeSize, fixedBinders) in cases do
    let name := owner ++ shortName
    let env ← getEnv
    let #[event] := (TemplateBinding.inventory env).filter (·.key.theoremName == name)
      | throwError "expected one original quantum registration"
    unless event.key.registrationModule == `Reg ++ owner do throwError "wrong source mirror"
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "original quantum claim absent"
    let before := (TemplateBinding.observedAssessments env).size
    let record ← TemplateBinding.assess event (some claim)
    unless (TemplateBinding.observedAssessments (← getEnv)).size == before + 1 do
      throwError "quantum evidence used a cached assessment"
    let .declaredValidated cert := record.result
      | throwError "quantum source failed: {(← TemplateBinding.recordJson record).compress}"
    unless cert.sourceBinding.isSome && record.escape.fromObject.isSome &&
        record.escape.bridgeKind == "source-equivalence" &&
        record.escape.continuation.any (·.kind == "open") do throwError "incomplete four slots"
    let some source := claim.escapeInput.sourceSelection | throwError "missing source selection"
    let info ← getConstInfo name
    let (scope, _) ← (SourceScope.resolve info source).run 524288
    let #[readout] := scope.readouts | throwError "expected the complete path readout"
    unless scope.telescope.size == telescope && source.coordinates == coordinates &&
        source.readouts[0]!.stateBinder == state && readout.context.size == scopeSize do throwError "quantum source scope changed"
    let levels := info.levelParams.map Level.param
    mustReject "wrong_owner" do
      discard <| (SourceScope.resolve info { source with owner := `D5.Other }).run 524288
    mustReject "absent_path" do
      discard <| (SourceScope.resolve info { source with readouts :=
        #[{ path := #["invalid"], stateBinder := state }] }).run 524288
    let outside := source.readouts.map (fun r => { r with stateBinder := scopeSize })
    mustReject "out_of_scope_state" do
      discard <| (SourceScope.resolve info { source with readouts := outside }).run 524288
    for binder in fixedBinders do
      mustReject s!"fixed_premise_as_coordinate_{binder}" do
        discard <| (SourceScope.resolve info { source with coordinates := #[binder] }).run 524288
    mustReject "erased_quantum" do
      discard <| (SourceScope.validateFields scope
        (mkConst (`Reg ++ owner ++ part ++ `signature)
          (levels.take (← getConstInfo (`Reg ++ owner ++ part ++ `signature)).levelParams.length))
        (mkConst (`Reg ++ owner ++ part ++ `rejected)
          (levels.take (← getConstInfo (`Reg ++ owner ++ part ++ `rejected)).levelParams.length))).run 524288
    mustReject "dropped_original_telescope" do
      discard <| (SourceScope.reconstruct info.type (mkConst ``True)).run 524288
    if shortName == `actual_source_moments then
      for clause in [:6] do
        let tail := if clause == 5 then [] else ["fn", "arg"]
        let path := List.replicate 4 "body" ++ ["arg", "body"] ++
          List.replicate clause "arg" ++ tail
        let weakened ← replaceAt info.type path (mkConst ``True)
        mustReject s!"dropped_circuit_born_or_moment_clause_{clause}" do
          discard <| (SourceScope.reconstruct info.type weakened).run 524288
    if shortName == `phase_history_bound then
      for branch in #[["fn", "arg"], ["arg"]] do
        let weakened ← replaceAt info.type (List.replicate 8 "body" ++ branch) (mkConst ``True)
        mustReject "dropped_PSD_conjunct" do
          discard <| (SourceScope.reconstruct info.type weakened).run 524288
      mustReject "fixed_reference_universe" do
        discard <| (SourceScope.reconstruct info.type
          (info.type.instantiateLevelParams info.levelParams [.zero])).run 524288
    if shortName == `result then
      for binder in [6:15] do
        let weakened ← replaceAt info.type (List.replicate binder "body" ++ ["domain"])
          (mkConst ``True)
        mustReject s!"dropped_curve_constraint_or_Fisher_bound_{binder}" do
          discard <| (SourceScope.reconstruct info.type weakened).run 524288
    for operand in #[mkConst name levels, info.type,
        mkApp (.lam `P (mkSort .zero) (mkConst ``Unit.unit) .default) info.type,
        mkApp (mkConst ``Decidable) info.type] do
      mustReject "theorem_answer_proof_or_dead_argument" do
        discard <| SourceOperands.check name #[operand] 524288
    selection := selection.push (event.key.registrationModule, #[event.key])
    logInfo m!"[PASS] {name} evidence_ref={cert.evidenceRef}"
  let owners := (selection.map (·.1)).toList.eraseDups.toArray
  selection := owners.map fun owner =>
    (owner, (selection.filter (·.1 == owner)).flatMap (·.2))
  IO.FS.writeFile ((← Repository.root) / ".lake/build/phase-fisher-source-evidence.json")
    ((Json.arr (← TemplateBinding.reportJson selection)).compress ++ "\n")

end LeanInformationAuditRegTests.PhaseFisherSourceContract
