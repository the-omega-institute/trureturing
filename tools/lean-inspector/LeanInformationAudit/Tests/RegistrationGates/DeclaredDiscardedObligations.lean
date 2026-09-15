import LeanInformationAudit.Tests.RegistrationGates.DeclaredObligations

namespace LeanInformationAudit.Tests.DeclaredDiscardedObligations
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open DeclaredObligations (boundProof)

def discardArgument (n : Nat) (_h : Nat.lt n (Nat.succ n)) :
    PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun x : Bool => x)

def expandedTemplate (n : Nat) : PrimitiveRealization (cutSignature Bool Bool) :=
  discardArgument n (boundProof n)

def betaTemplate (n : Nat) : PrimitiveRealization (cutSignature Bool Bool) :=
  (fun (_h : Nat.lt n (Nat.succ n)) =>
    cutRealization (fun x : Bool => x)) (boundProof n)

register_information_template expandedTemplate
register_information_template betaTemplate

def betaHeadTemplate (n : Nat) : PrimitiveRealization (cutSignature Bool Bool) :=
  (fun (_h : Nat.lt n (Nat.succ n)) => fun b : Bool =>
    cutRealization (fun _x : Bool => b)) (boundProof n) true

register_information_template betaHeadTemplate

def targetArena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law _ := Nat.lt 0 (Nat.succ 0)

def independentArena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law _ := Nat.lt 1 (Nat.succ 1)

instance : DecidableEq targetArena.State := instDecidableEqBool
instance : DecidableEq independentArena.State := instDecidableEqBool

information_theorem expandedTarget in targetArena primitives (expandedTemplate 0)
  : Nat.lt 0 (Nat.succ 0) := Nat.zero_lt_succ 0
information_theorem expandedIndependent in independentArena primitives (expandedTemplate 0)
  : Nat.lt 1 (Nat.succ 1) := Nat.lt_succ_self 1
information_theorem betaTarget in targetArena primitives (betaTemplate 0)
  : Nat.lt 0 (Nat.succ 0) := Nat.zero_lt_succ 0
information_theorem betaIndependent in independentArena primitives (betaTemplate 0)
  : Nat.lt 1 (Nat.succ 1) := Nat.lt_succ_self 1
information_theorem betaHeadTarget in targetArena primitives (betaHeadTemplate 0)
  : Nat.lt 0 (Nat.succ 0) := Nat.zero_lt_succ 0
information_theorem betaHeadIndependent in independentArena primitives (betaHeadTemplate 0)
  : Nat.lt 1 (Nat.succ 1) := Nat.lt_succ_self 1

run_meta do
  for (name, template, label, shouldValidate) in #[
      (``expandedTarget, ``expandedTemplate, "expanded_discarded_proof_type_rejected", false),
      (``expandedIndependent, ``expandedTemplate, "expanded_independent_proof_type_accepted", true),
      (``betaTarget, ``betaTemplate, "beta_discarded_proof_type_rejected", false),
      (``betaIndependent, ``betaTemplate, "beta_independent_proof_type_accepted", true),
      (``betaHeadTarget, ``betaHeadTemplate, "beta_head_discarded_proof_type_rejected", false),
      (``betaHeadIndependent, ``betaHeadTemplate, "beta_head_independent_proof_type_accepted", true)] do
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
    logInfo m!"[{if ok then "PASS" else "FAIL"}] {label}"
    unless ok do logInfo m!"actual={result}"

end LeanInformationAudit.Tests.DeclaredDiscardedObligations
