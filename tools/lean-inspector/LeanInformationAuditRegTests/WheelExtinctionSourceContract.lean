import Reg.D5.S3.Combinatorics.WheelHivExtinctionRefutation
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.WheelExtinctionSourceContract

private def mustReject (rule : String) (action : MetaM Unit) : MetaM Unit := do
  let result ← try action; pure "accepted" catch e => e.toMessageData.toString
  unless result.contains rule do throwError "expected {rule}, got {result}"
  logInfo m!"[PASS] {rule}"

run_meta do
  let owner := `D5.S3.Combinatorics.WheelHivExtinctionRefutation
  let target := owner ++ `result
  let env ← getEnv
  let some event := (TemplateBinding.inventory env).find? (·.key.theoremName == target)
    | throwError "missing original occurrence"
  let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
    | throwError "missing source claim"
  let record ← TemplateBinding.assess event (some claim)
  let .declaredValidated _ := record.result
    | throwError "registration rejected: {(← TemplateBinding.recordJson record).compress}"
  unless record.escape.fromObject.isSome && record.escape.bridgeKind == "source-equivalence" &&
      record.escape.continuation.any (·.kind == "open") do throwError "incomplete four slots"
  let some selection := claim.escapeInput.sourceSelection | throwError "missing source selection"
  let info ← getConstInfo target
  let (scope, _) ← (SourceScope.resolve info selection).run 524288
  let some definition := scope.definition | throwError "missing original named entry"
  unless definition.name == owner ++ `claim && info.type.equal (mkApp (mkConst ``Not) (mkConst (owner ++ `claim))) do
    throwError "wrong exact source"
  mustReject "source.absent_occurrence" do
    discard <| (SourceScope.resolve info { selection with definition := none }).run 524288
  mustReject "source.actual_observation" do
    discard <| (SourceScope.validateFields scope
      (mkConst `Reg.Support.WheelExtinctionSource.signature)
      (mkConst `Reg.Support.WheelExtinctionSource.rejected)).run 524288
  unless definition.value.isAppOfArity ``And 2 do throwError "original parity branches absent"
  mustReject "source.statement_reconstruction" do
    discard <| (SourceScope.reconstruct definition.value definition.value.getAppArgs[0]!).run 524288
  mustReject "source.statement_reconstruction" do
    discard <| (SourceScope.reconstruct definition.value
      (mkApp2 (mkConst ``Or) definition.value.getAppArgs[0]! definition.value.getAppArgs[1]!)).run 524288
  mustReject "source.definition_reference" do
    let some entry := selection.definition | throwError "entry absent"
    discard <| (SourceScope.resolve info { selection with definition := some { entry with path := #[] } }).run 524288
  -- The odd branch uses the identical full state-indexed observation. Check
  -- its independent raw occurrence against the very same actual family.
  let oddSelection := { selection with readouts := #[{
    path := #["arg", "arg", "body", "body", "body", "fn", "arg"]
    stateBinder := 0 }] }
  let (oddScope, _) ← (SourceScope.resolve info oddSelection).run 524288
  discard <| (SourceScope.validateFields oddScope
    (mkConst `Reg.Support.WheelExtinctionSource.signature)
    (mkConst `Reg.Support.WheelExtinctionSource.actual)).run 524288
  for name in #[target, event.realizationName] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "nonstandard axiom closure"
  logInfo m!"[PASS] complete negated two-parity source and four-slot contract"

end LeanInformationAuditRegTests.WheelExtinctionSourceContract
