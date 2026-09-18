import LeanInformationAudit.Syntax

namespace LeanInformationAudit.Tests.DeclaredArguments
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape

theorem target : (137 : Nat) = 137 := rfl
theorem identityTarget : ∀ x : Bool, x = x.not.not := fun x => (Bool.not_not x).symm
theorem independent : True := True.intro
def discardTarget (_ : (137 : Nat) = 137) : Arena := Arena.ofFintype Bool
def discardClean (_ : True) : Arena := Arena.ofFintype Bool
def nestedTarget := Option (Arena.State (discardTarget target))
def nestedClean := Option (Arena.State (discardClean independent))
def closedDecision (_ : Bool) : Bool := decide ((0 : Nat) < 24)
def recursiveArgument (n : Nat) : Bool := Nat.rec true (fun _ b => b) n
def identity (x : Bool) : Bool := x
def keep {p : Prop} (_ : p) (x : Bool) : Bool := x
def hidden (x : Bool) : Bool := let h := identityTarget; keep h x
def targetDecision : Decidable (∀ x : Bool, x = x.not.not) := .isTrue identityTarget
structure TargetCarrier where
  bit : Bool
  proof : (137 : Nat) = 137
def carrier : TargetCarrier := ⟨true, rfl⟩
class UnknownCarrier where
  bit : Bool
def unknown : UnknownCarrier := ⟨true⟩
def independentPair : Bool × Bool := (true, false)
def companion.__information_unit (x : Bool) : Bool := x

private def check (label : String) (argument : Expr) (expected : Option String)
    (work : Nat := 524288) (theoremName : Name := ``target) : MetaM Unit := do
  let saved ← getEnv
  let result ← RegistrationGates.templateArgumentsCurrent theoremName #[argument] work
  let actual := match result with
    | .ok _ => none
    | .error diagnostic => some diagnostic
  setEnv saved
  (if actual == expected then logInfo else logError) m!"[{if actual == expected then "PASS" else "FAIL"}] {label} result={repr actual}"

-- Independently typed arguments pass through the production entry used by
-- TemplateBinding.validate and P1. Every case restores the environment so
-- syntax-summary memoization cannot make the next oracle self-referential.
run_meta do
  let .defnInfo bad ← getConstInfo ``nestedTarget | throwError "setup"
  let .defnInfo clean ← getConstInfo ``nestedClean | throwError "setup"
  check "raw_carrier_target_proof_rejected" bad.value
    (some "forbidden_dependency:dtr.argument_audit")
  check "raw_carrier_clean_twin_accepted" clean.value none
  let .defnInfo closedDecisionInfo ← getConstInfo ``closedDecision | throwError "setup"
  let decisionResult ← RegistrationGates.templateArgumentsCurrent ``target #[closedDecisionInfo.value] 524288
  let rejected := match decisionResult with
    | .error s => s == "unclassified_form:E3.closed_decision"
    | _ => false
  (if rejected then logInfo else logError) m!"[{if rejected then "PASS" else "FAIL"}] argument_closed_decision_grammar_rejected result={repr decisionResult}"
  let .defnInfo recursiveInfo ← getConstInfo ``recursiveArgument | throwError "setup"
  check "argument_unsupported_nat_recursion_rejected" recursiveInfo.value
    (some "unclassified_form:E4.recursion:Nat.rec")
  let .defnInfo identityInfo ← getConstInfo ``identity | throwError "setup"
  check "independent_data_argument_accepted" identityInfo.value none
  check "independent_proof_and_dictionary_accepted" (mkConst ``independent) none
  check "object_projection_accepted"
    (.proj ``Prod 0 (mkConst ``independentPair)) none
  check "nonindex_numeric_encoding_rejected" (mkNatLit 0)
    (some "unclassified_form:E3.index_encoding:OfNat.ofNat")
  check "nonindex_numeric_literal_rejected" (.lit (.natVal 0))
    (some "unclassified_form:E3.nonindex_literal")
  check "bounded_admitted_arguments_accepted" (mkConst ``Bool.true) none
  check "argument_theorem_direct_rejected" (mkConst ``identityTarget)
    (some "forbidden_dependency:dtr.argument_audit") 524288 ``identityTarget
  let .defnInfo hiddenInfo ← getConstInfo ``hidden | throwError "setup"
  check "argument_theorem_helper_let_rejected" hiddenInfo.value
    (some "forbidden_dependency:dtr.argument_audit") 524288 ``identityTarget
  check "argument_theorem_instance_rejected" (mkConst ``targetDecision)
    (some "forbidden_dependency:dtr.argument_audit") 524288 ``identityTarget
  let type := (← getConstInfo ``target).type
  let proof ← mkEqRefl (mkNatLit 137)
  check "argument_statement_proof_rejected" proof
    (some "forbidden_dependency:dtr.argument_audit")
  let decision ← mkAppM ``Decidable.isTrue #[proof]
  unless (← inferType decision).isAppOfArity ``Decidable 1 do
    throwError "setup: expected a typed decision"
  check "argument_statement_decision_rejected" decision
    (some "forbidden_dependency:dtr.argument_audit")
  check "argument_statement_carrier_rejected" (mkConst ``carrier)
    (some "unclassified_form:E2.unknown_constant:LeanInformationAudit.Tests.DeclaredArguments.TargetCarrier")
  check "argument_certificate_projection_rejected" (mkConst ``InformationRegistryEntry.statementIdentity)
    (some "forbidden_dependency:dtr.argument_audit")
  check "argument_generated_identity_rejected" (mkConst ``companion.__information_unit)
    (some "forbidden_dependency:dtr.argument_audit")
  check "argument_statement_hash_rejected" (mkConst ``Sha256.hex)
    (some "forbidden_dependency:dtr.argument_audit")
  check "argument_unknown_carrier_rejected" (mkConst ``unknown)
    (some "unclassified_form:E2.unknown_constant:LeanInformationAudit.Tests.DeclaredArguments.UnknownCarrier")
  check "argument_exhaustion_incomplete" (mkConst ``Bool.true)
    (some "incomplete_closure:E8.argument_work") 0
  unless (← inferType proof).equal type do throwError "setup: statement proof type differs"

end LeanInformationAudit.Tests.DeclaredArguments
