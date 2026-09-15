import LeanInformationAudit.Tests.RegistrationGates.DeclaredDiscardedObligations

namespace LeanInformationAudit.Tests.DeclaredTelescopeObligations
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open DeclaredObligations (boundProof)
open DeclaredDiscardedObligations (targetArena independentArena)

def hideProof (n : Nat) (_h : Nat.lt n (Nat.succ n)) : Type := Bool

def domainTemplate (n : Nat) :
    hideProof n (boundProof n) → PrimitiveRealization (cutSignature Bool Bool) :=
  fun (b : Bool) => cutRealization (fun _ : Bool => b)

def bodyDomainTemplate (n : Nat) :
    Bool → PrimitiveRealization (cutSignature Bool Bool) :=
  fun (b : hideProof n (boundProof n)) => cutRealization (fun _ : Bool => b)

run_meta do
  for (name, publicHidden, bodyHidden) in
      #[( ``domainTemplate, true, false), (``bodyDomainTemplate, false, true)] do
    let some (.defnInfo info) := (← getEnv).find? name | throwError "setup: missing definition"
    let .forallE _ _ (.forallE _ domain _ _) _ := info.type
      | throwError "setup: public telescope shape"
    let .lam _ _ (.lam _ bodyDomain _ _) _ := info.value
      | throwError "setup: body telescope shape"
    unless domain.getAppFn.isConstOf (if publicHidden then ``hideProof else ``Bool) &&
        bodyDomain.getAppFn.isConstOf (if bodyHidden then ``hideProof else ``Bool) do
      throwError "setup: telescope domains do not isolate public/body paths"
    logInfo m!"[PASS] raw_telescope_domains_isolate_{name}"

register_information_template domainTemplate
register_information_template bodyDomainTemplate

information_theorem domainTarget in targetArena primitives (domainTemplate 0 true)
  : Nat.lt 0 (Nat.succ 0) := Nat.zero_lt_succ 0
information_theorem domainIndependent in independentArena primitives (domainTemplate 0 true)
  : Nat.lt 1 (Nat.succ 1) := Nat.lt_succ_self 1
information_theorem bodyDomainTarget in targetArena primitives (bodyDomainTemplate 0 true)
  : Nat.lt 0 (Nat.succ 0) := Nat.zero_lt_succ 0
information_theorem bodyDomainIndependent in independentArena primitives (bodyDomainTemplate 0 true)
  : Nat.lt 1 (Nat.succ 1) := Nat.lt_succ_self 1

run_meta do
  for (name, template, label, shouldValidate) in #[
      (``domainTarget, ``domainTemplate, "telescope_discarded_proof_type_rejected", false),
      (``domainIndependent, ``domainTemplate, "telescope_independent_proof_type_accepted", true),
      (``bodyDomainTarget, ``bodyDomainTemplate, "body_telescope_discarded_proof_type_rejected", false),
      (``bodyDomainIndependent, ``bodyDomainTemplate, "body_telescope_independent_proof_type_accepted", true)] do
    let some event := (TemplateBinding.inventory (← getEnv)).find? (·.key.theoremName == name)
      | throwError "setup: missing native registration"
    let descriptor ← mkAppM template #[mkNatLit 0, mkConst ``Bool.true]
    let record ← TemplateBinding.assess event (some {
      key := event.key, arena := event.arena, descriptor := some descriptor,
      owner := (← getEnv).header.mainModule })
    let (ok, result) := match record.result with
      | .declaredValidated _ => (shouldValidate, "validated")
      | .declaredUnresolved diagnostic =>
        (!shouldValidate && (diagnostic.splitOn
          "reason=forbidden_dependency rule=dtr.instantiated_type site=").length == 2, diagnostic)
      | .undeclared => (false, "undeclared")
    logInfo m!"[{if ok then "PASS" else "FAIL"}] {label}"
    unless ok do logInfo m!"actual={result}"

end LeanInformationAudit.Tests.DeclaredTelescopeObligations
