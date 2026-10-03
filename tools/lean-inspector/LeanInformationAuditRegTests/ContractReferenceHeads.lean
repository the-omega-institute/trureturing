import LeanInformationAuditRegTests.ContractGuards

namespace LeanInformationAuditRegTests.ContractReferenceHeads
open Lean Meta Elab Command LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

private def refExpr (value : Expr) : Expr :=
  mkApp2 (mkConst ``Ref.mk [.succ .zero]) (mkConst ``Nat) value

def lambdaPayload : Ref (Nat → Nat) := { value := fun n => n }
def letPayload : Ref Nat := { value := let n := Nat.zero; Nat.succ n }
def pairValue : Nat × Nat := (Nat.zero, Nat.zero)
def projectionPayload : Ref Nat := {
  value := by_elab pure (Lean.Expr.proj ``Prod 0 (Lean.mkConst ``pairValue)) }

run_meta do
  for (label, name) in #[
      ("lambda", ``lambdaPayload), ("let", ``letPayload), ("projection", ``projectionPayload)] do
    let info ← getConstInfo name
    let error ← try
      discard <| Decoder.reference "arena" info.value!
      pure "accepted"
    catch ex => ex.toMessageData.toString
    assertTest s!"reference.head.compiled.{label}"
      (error.startsWith "unclassified_form:contract.reference_head:arena")
  let zero := mkConst ``Nat.zero
  let values := #[
    ("constant", zero, ``Nat.zero),
    ("application", mkApp (mkConst ``Nat.succ) zero, ``Nat.succ),
    ("outer_metadata", .mdata {} zero, ``Nat.zero),
    ("function_metadata", mkApp (.mdata {} (mkConst ``Nat.succ)) zero, ``Nat.succ),
    ("nested_metadata", .mdata {} (mkApp (.mdata {} (mkConst ``Nat.succ)) zero), ``Nat.succ)]
  for (label, value, expected) in values do
    let decoded ← try
      pure (some (← Decoder.reference "arena" (refExpr value)))
    catch _ => pure none
    assertTest s!"reference.head.positive.{label}"
      (decoded.any fun (name, payload) => name == expected && payload == value)
  let negatives : Array (String × Expr × String) := #[
    ("lambda", .lam `x (mkConst ``Nat) (.bvar 0) .default, "unclassified_form:contract.reference_head:"),
    ("let", .letE `x (mkConst ``Nat) zero (.bvar 0) false, "unclassified_form:contract.reference_head:"),
    ("projection", .proj ``Prod 0 zero, "unclassified_form:contract.reference_head:"),
    ("bound", .bvar 0, "incomplete_closure:contract.reference_open:"),
    ("free", .fvar ⟨`x⟩, "incomplete_closure:contract.reference_open:"),
    ("metavariable", .mvar ⟨`x⟩, "incomplete_closure:contract.reference_open:"),
    ("unknown", mkConst `ContractTests.missingConstant, "unclassified_form:contract.reference_unknown:")]
  for role in #["arena", "object_arena", "realization", "variation", "sensitivity",
      "continuation", "family_record"] do
    for (label, value, diagnostic) in negatives do
      let error ← try
        discard <| Decoder.reference role (refExpr value)
        pure "accepted"
      catch ex => ex.toMessageData.toString
      assertTest s!"reference.head.negative.{role}.{label}"
        (error.startsWith (diagnostic ++ role))
      logInfo m!"CONTRACT_DIAGNOSTIC reference.head.{role}.{label} {error}"
  let source ← ofExcept <| Parser.runParserCategory (← getEnv) `term
    "{ name := `Nat.zero, value := Nat.zero }"
  let result := SourceLiteral.audit (← getEnv) (.record ``Ref) source "reference"
  assertTest "reference.schema.removed_name" (match result with
    | .error error => error.startsWith "contract.source_literal:nonliteral:reference:"
    | .ok _ => false)
  let source ← ofExcept <| Parser.runParserCategory (← getEnv) `term "{ value := Nat.zero }"
  assertTest "reference.schema.value_only"
    (SourceLiteral.audit (← getEnv) (.record ``Ref) source "reference").isOk

end LeanInformationAuditRegTests.ContractReferenceHeads
