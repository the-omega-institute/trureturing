import LeanInformationAuditRegTests.ContractFixtures
import LeanInformationAuditRegTests.ContractGuards

namespace LeanInformationAuditRegTests.ContractTargetHead
open Lean Meta Elab Command LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

run_meta do
  let owner := `LeanInformationAuditRegTests.ContractFixtures
  for index in [0, 1] do
    let .defnInfo info ← getConstInfo (owner.str s!"source{index}")
      | throwError "setup:registration_definition"
    let target := info.type.getAppArgs[1]!
    logInfo m!"CONTRACT_UNIVERSE_APPLICATION {(Json.mkObj [
      ("index", toJson index),
      ("levels", toJson (info.type.getAppFn.constLevels!.map toString)),
      ("carrier_levels", toJson ((info.type.getAppArgs.extract 2 4).map fun carrier =>
        carrier.getAppFn.constLevels!.map toString))]).compress}"
    let decoded ← try
      pure (some (← Decoder.registration owner info ""))
    catch _ => pure none
    assertTest s!"target.name.derived.{index}" (decoded.any fun row =>
      row.input.entry.theoremName == target.constName! && row.target == target)
  let .defnInfo info ← getConstInfo ``LeanInformationAuditRegTests.ContractFixtures.source0
    | throwError "setup:target_fixture"
  let args := info.type.getAppArgs
  let target := args[1]!
  let bad : Array (String × Expr × String) := #[
    ("lambda", .lam `x (mkConst ``Nat) (.bvar 0) .default, "unclassified_form:contract.reference_head:target"),
    ("let", .letE `x (mkConst ``Nat) (mkConst ``Nat.zero) (.bvar 0) false,
      "unclassified_form:contract.reference_head:target"),
    ("projection", .proj ``Prod 0 (mkConst ``Nat.zero), "unclassified_form:contract.reference_head:target"),
    ("open", .bvar 0, "incomplete_closure:contract.reference_open:target"),
    ("unknown", mkConst `ContractTests.missingTarget, "unclassified_form:contract.reference_unknown:target"),
    ("definition", mkConst ``Nat.zero, "unclassified_form:contract.target_theorem:")]
  for (label, value, diagnostic) in bad do
    let candidate := { info with type := mkAppN info.type.getAppFn (args.set! 1 value) }
    let error ← try
      discard <| Decoder.registration owner candidate ""
      pure "accepted"
    catch ex => ex.toMessageData.toString
    assertTest s!"target.negative.{label}" (error.startsWith diagnostic)
  let candidate := { info with type := mkAppN info.type.getAppFn args.pop }
  let error ← try
    discard <| Decoder.registration owner candidate ""
    pure "accepted"
  catch ex => ex.toMessageData.toString
  assertTest "target.negative.arity" (error.startsWith "contract.registration:target_arity")
  assertTest "target.fixture.closed" (Literal.closed target)

end LeanInformationAuditRegTests.ContractTargetHead
