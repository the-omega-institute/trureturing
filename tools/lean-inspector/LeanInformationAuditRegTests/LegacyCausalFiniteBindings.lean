import LeanInformationAuditRegTests.LegacyAssignedTransport
import LeanInformationAuditRegTests.LegacyContextCausalBindings

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.LegacyCausalFiniteBindings

run_meta do
  let env ← getEnv
  let excluded := #[
    `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause,
    `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary,
    `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application]
  let all := Reg.Support.SharedInformationRootContract.contract.expected ++
    Reg.Support.TemplateShadowContract.contract.expected
  let expected := all.filter (fun row => !excluded.contains row.theoremName)
  unless all.size == 23 && expected.size == 18 do throwError "legacy scope changed"
  let inventory := TemplateBinding.inventory env
  let mut selected := #[]
  for row in expected do
    let #[event] := inventory.filter (fun e =>
      e.key.registrationModule == row.registrationModuleName && e.key.theoremName == row.theoremName)
      | throwError "historical occurrence missing or duplicated: {row.registrationModuleName}"
    unless event.key.objectArena == row.objectArenaName do throwError "historical arena retargeted"
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "missing original declaration"
    let record ← TemplateBinding.assess event (some claim)
    let .declaredValidated certificate := record.result
      | throwError "original binding failed: {(← TemplateBinding.recordJson record).compress}"
    unless record.escape.fromObject.isSome &&
        record.escape.continuation.any (·.kind == "open") &&
        !certificate.evidenceRef.isEmpty do throwError "missing four-slot evidence"
    unless (← TemplateBinding.assess event none).result matches .undeclared do
      throwError "missing descriptor accepted"
    for changed in #[
        { event with realizationName := `Reg.Invalid.missingRealization },
        { event with key := { event.key with theoremName := ``True.intro } },
        { event with key := { event.key with objectArena := `Reg.Invalid.changedLaw } }] do
      if (← TemplateBinding.assess changed (some claim)).result matches .declaredValidated _ then
        throwError "missing realization or wrong occurrence accepted"
    selected := selected.push (row.registrationModuleName, #[event.key])
  for (arena, sensitivityName) in #[
      (``Reg.Support.LegacyCausalSlots.localArena, ``Reg.Support.LegacyCausalSlots.local_sensitivity),
      (``Reg.Support.LegacyCausalSlots.icArena, ``Reg.Support.LegacyCausalSlots.ic_sensitivity),
      (``Reg.Support.LegacyCausalSlots.oiArena, ``Reg.Support.LegacyCausalSlots.oi_sensitivity)] do
    let altered ← mkAppM ``LegacyAssignedTransport.alteredLaw #[mkConst arena]
    let expectedType ← mkAppM ``FiniteSlotSensitivity #[altered]
    if ← RegistrationGates.checked sensitivityName expectedType then
      throwError "original sensitivity accepted for a constant-true Law"
  let wire := Json.arr (← TemplateBinding.reportJson selected)
  IO.FS.writeFile ((← Repository.root) / ".lake/build/legacy-causal-final.json") (wire.compress ++ "\n")
  logInfo "[PASS] all 18 historical occurrences validate; missing declaration/realization, wrong occurrence and changed Law reject"

end LeanInformationAuditRegTests.LegacyCausalFiniteBindings
