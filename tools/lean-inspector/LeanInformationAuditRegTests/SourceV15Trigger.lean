import Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot
import Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.InformationRoot

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.SourceV15Trigger

-- Temporary real-event reject payload with positive controls: both original finite catalog occurrences,
-- including Preemption's explicit state/predicate and Completion's function operands.
run_meta do
  let env ← getEnv
  let owners := #[
    `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot,
    `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.InformationRoot]
  let events := (TemplateBinding.inventory env).filter (owners.contains ∘ (·.key.registrationModule))
  unless events.size == 2 do throwError "expected both original occurrences"
  let family := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily
  for event in events do
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "missing original claim"
    let record ← TemplateBinding.assess event (some claim)
    let .declaredValidated certificate := record.result
      | throwError "allow rejected: {(← TemplateBinding.recordJson record).compress}"
    unless certificate.sourceBinding.isSome && record.escape.fromObject.isSome &&
        record.escape.continuation.any (·.kind == "open") &&
        record.escape.bridgeKind == "source-equivalence" do
      throwError "missing original four-slot evidence"
    let source ← getConstInfo event.key.theoremName
    let selection := claim.escapeInput.sourceSelection.get!
    let (scope, _) ← (SourceScope.resolve source selection).run 524288
    let registration := mkConst event.realizationName
    let registrationType ← inferType registration
    unless ← isDefEq registrationType.getAppArgs[1]! source.type do
      throwError "original statement changed"
    checkWithKernel registration
    let arena := registrationType.getAppArgs[0]!
    let signature ← mkAppM (family ++ `Arena.signature) #[arena]
    let actual ← mkAppM (family ++ `Registration.actual) #[registration]
    let law ← mkAppM (family ++ `Arena.Law) #[arena, actual]
    discard <| (SourceScope.reconstruct scope.expanded law).run 524288
    discard <| (SourceFinite.validate event arena signature actual
      claim.escapeInput.finiteBridge.get!).run 524288
    logInfo m!"[PASS] v15 allow full source and finite Law: {event.key.theoremName}; evidence={certificate.evidenceRef}"
  let exported ← TemplateBinding.reportJson (owners.map fun owner =>
    (owner, events.filter (·.key.registrationModule == owner) |>.map (·.key)))
  let root ← Repository.root
  let fixture ← IO.ofExcept <| Json.parse (← IO.FS.readFile
    (root / "tools/tests/StrataLint.DeclaredTemplate.Tests/SourceV15Trigger.json"))
  let expected ← IO.ofExcept (fixture.getObjValAs? (Array Json) "wires")
  unless exported.map Json.compress == expected.map Json.compress do
    throwError "native report fixture differs from current original source exporter"
  IO.FS.writeFile (root / ".lake/build/source-v15-trigger-allow.json")
    ((Json.arr exported).compress ++ "\n")
  logInfo "[PASS] v15 reject controls preserve both full Laws and native correspondence"
  let mut rejected := #[]
  for event in events do
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "missing original claim"
    let preemption := event.key.registrationModule == owners[0]!
    let selection := claim.escapeInput.sourceSelection.get!
    -- Both Completion paths exist, have the same type and name actual source
    -- functions. Swapping them must fail correspondence, not parsing or typing.
    let swapped := selection.readouts.set! 0 selection.readouts[1]!
      |>.set! 1 selection.readouts[0]!
    let swappedSelection := {selection with readouts := swapped}
    let wrongInput := if preemption then
        {claim.escapeInput with
          finiteBridge := some `Reg.Support.LegacyRelations.Preemption.registration}
      else
        {claim.escapeInput with sourceSelection := some swappedSelection}
    let wrong := {claim with escapeInput := wrongInput}
    let rule := if preemption then "source.finite_bridge" else "source.actual_observation"
    let record ← TemplateBinding.assess event (some wrong)
    let .declaredUnresolved diagnostic := record.result
      | throwError "v15 reject admitted {rule}"
    unless diagnostic.startsWith "IE-C050 ClosedTruthReadout " &&
        diagnostic.contains ("rule=" ++ rule ++ " ") do
      throwError "expected IE-C050/{rule}, got {diagnostic}"
    let wire ← TemplateBinding.recordJson record
    unless (← IO.ofExcept (wire.getObjVal? "certificate")) == Json.null do
      throwError "rejection carried a certificate"
    rejected := rejected.push wire
    logInfo m!"[PASS] v15 reject {diagnostic}; certificate=null"
  -- The full finite Law must also agree for arbitrary realizations, even when
  -- the actual realization still satisfies a proposed weaker Law.
  let some event := events.find? (·.key.registrationModule == owners[0]!)
    | throwError "missing preemption occurrence"
  let support := `Reg.Support.LegacyRelations.Preemption
  let signature := mkConst (support ++ `signature)
  let actual := mkConst (support ++ `actual)
  let weakLaw ← withLocalDeclD `r (← mkAppM (family ++ `Realization) #[signature]) fun r =>
    mkLambdaFVars #[r] (mkConst ``True)
  let weakArena ← mkAppM (family ++ `Arena.mk) #[signature, weakLaw]
  let bridge := `D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_realization
  let reason ← try
    discard <| (SourceFinite.validate event weakArena signature actual bridge).run 524288
    pure "accepted"
    catch error => error.toMessageData.toString
  unless reason == "unclassified_form:source.finite_full_law" do
    throwError "expected source.finite_full_law, got {reason}"
  logInfo m!"[PASS] v15 reject arbitrary-realization Law: {reason}"
  IO.FS.writeFile (root / ".lake/build/source-v15-trigger-reject.json")
    ((Json.arr rejected).compress ++ "\n")
  let expectedRejected ← IO.ofExcept (fixture.getObjValAs? (Array Json) "rejected")
  unless rejected.map Json.compress == expectedRejected.map Json.compress do
    throwError "current rejected records differ from native consumer fixture"
  logInfo "[PASS] v15 reject current compiler records equal managed consumer fixture"

end LeanInformationAuditRegTests.SourceV15Trigger
