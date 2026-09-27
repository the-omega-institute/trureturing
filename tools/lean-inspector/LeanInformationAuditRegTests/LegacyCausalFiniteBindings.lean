import LeanInformationAuditRegTests.LegacyAssignedTransport
import LeanInformationAuditRegTests.LegacyContextCausalBindings

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.LegacyCausalFiniteBindings

run_meta do
  let env ← getEnv
  let expected := Reg.Support.SharedInformationRootContract.contract.expected ++
    Reg.Support.TemplateShadowContract.contract.expected
  unless expected.size == 23 do throwError "legacy scope changed"
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
    let missingRealization ← try
        discard <| TemplateBinding.assess
          { event with realizationName := `Reg.Invalid.missingRealization } (some claim)
        pure "accepted"
      catch error => error.toMessageData.toString
    unless missingRealization == "Unknown constant `Reg.Invalid.missingRealization`" do
      throwError "unexpected missing realization result: {missingRealization}"
    for changed in #[
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
  logInfo "[PASS] all 23 historical occurrences validate; missing declaration/realization, wrong occurrence and changed Law reject"

end LeanInformationAuditRegTests.LegacyCausalFiniteBindings
