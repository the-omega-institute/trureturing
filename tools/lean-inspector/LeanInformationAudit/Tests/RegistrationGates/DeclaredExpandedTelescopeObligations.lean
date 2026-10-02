import LeanInformationAudit.Tests.RegistrationGates.DeclaredTelescopeObligations
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

namespace LeanInformationAudit.Tests.DeclaredExpandedTelescopeObligations
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open DeclaredDiscardedObligations (targetArena independentArena)
open DeclaredTelescopeObligations (domainTemplate bodyDomainTemplate)

def expandedDomainTemplate (n : Nat) : PrimitiveRealization (cutSignature Bool Bool) :=
  domainTemplate n true

def expandedBodyDomainTemplate (n : Nat) : PrimitiveRealization (cutSignature Bool Bool) :=
  bodyDomainTemplate n true

test_assess in register_information_template expandedDomainTemplate
test_assess in register_information_template expandedBodyDomainTemplate

test_assess in information_theorem expandedDomainTarget in targetArena primitives (expandedDomainTemplate 0)
  : Nat.lt 0 (Nat.succ 0) := Nat.zero_lt_succ 0
test_assess in information_theorem expandedDomainIndependent in independentArena primitives (expandedDomainTemplate 0)
  : Nat.lt 1 (Nat.succ 1) := Nat.lt_succ_self 1
test_assess in information_theorem expandedBodyDomainTarget in targetArena primitives (expandedBodyDomainTemplate 0)
  : Nat.lt 0 (Nat.succ 0) := Nat.zero_lt_succ 0
test_assess in information_theorem expandedBodyDomainIndependent in independentArena primitives (expandedBodyDomainTemplate 0)
  : Nat.lt 1 (Nat.succ 1) := Nat.lt_succ_self 1

run_meta do
  for (name, template, label, shouldValidate) in #[
      (``expandedDomainTarget, ``expandedDomainTemplate, "expanded_telescope_discarded_proof_type_rejected", false),
      (``expandedDomainIndependent, ``expandedDomainTemplate, "expanded_telescope_independent_proof_type_accepted", true),
      (``expandedBodyDomainTarget, ``expandedBodyDomainTemplate, "expanded_body_telescope_discarded_proof_type_rejected", false),
      (``expandedBodyDomainIndependent, ``expandedBodyDomainTemplate, "expanded_body_telescope_independent_proof_type_accepted", true)] do
    let some event := (TemplateBinding.inventory (← getEnv)).find? (·.key.theoremName == name)
      | throwError "setup: missing native registration"
    let descriptor ← mkAppM template #[mkNatLit 0]
    let record ← TemplateBinding.assess event (some {
      key := event.key, arena := event.arena, descriptor := some descriptor,
      owner := (← getEnv).header.mainModule })
    let (ok, result) := match record.result with
      | .declaredValidated _ => (shouldValidate, "validated")
      | .declaredUnresolved diagnostic =>
        (!shouldValidate && (diagnostic.splitOn
          "reason=forbidden_dependency rule=dtr.instantiated_type site=").length == 2, diagnostic)
      | .undeclared => (false, "undeclared")
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"
    unless ok do logInfo m!"actual={result}"

end LeanInformationAudit.Tests.DeclaredExpandedTelescopeObligations
