import LeanInformationAudit.Tests.RegistrationGates.DeclaredDiscardedObligations

namespace LeanInformationAudit.Tests.DeclaredResultTypeObligations
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open DeclaredObligations (boundProof)
open DeclaredDiscardedObligations (targetArena independentArena)

def resultType (n : Nat) (_h : Nat.lt n (Nat.succ n)) : Type :=
  PrimitiveRealization (cutSignature Bool Bool)

def resultHelper (n : Nat) : resultType n (boundProof n) :=
  cutRealization (fun x : Bool => x)

def template (n : Nat) : PrimitiveRealization (cutSignature Bool Bool) := resultHelper n

register_information_template template

information_theorem expandedDomainTarget in targetArena primitives (template 0)
  : Nat.lt 0 (Nat.succ 0) := Nat.zero_lt_succ 0
information_theorem expandedDomainIndependent in independentArena primitives (template 0)
  : Nat.lt 1 (Nat.succ 1) := Nat.lt_succ_self 1
run_meta do
  for (name, template, label, shouldValidate) in #[
      (``expandedDomainTarget, ``template, "expanded_result_type_discarded_proof_rejected", false),
      (``expandedDomainIndependent, ``template, "expanded_result_type_independent_proof_accepted", true)] do
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


end LeanInformationAudit.Tests.DeclaredResultTypeObligations
