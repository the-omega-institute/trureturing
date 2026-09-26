import Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot
import Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.InformationRoot

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.SourceV15Trigger

-- Temporary real-event allow payload: both original finite catalog occurrences,
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
  logInfo "[PASS] v15 allow current compiler export equals native consumer fixture"

end LeanInformationAuditRegTests.SourceV15Trigger
