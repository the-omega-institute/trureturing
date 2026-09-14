import LeanInformationAudit.Tests.RegistrationGates.DeclaredBindings

namespace LeanInformationAudit.Tests.DeclaredObligations
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

theorem boundProof (n : Nat) : Nat.lt n (Nat.succ n) := Nat.lt_succ_self n

def boundTemplate (n : Nat) : PrimitiveRealization (cutSignature Bool (Fin (Nat.succ n))) :=
  cutRealization (fun _ : Bool => ⟨n, boundProof n⟩)

register_information_template boundTemplate

def indexedDecision (P : Bool → Prop) (d : ∀ b, Decidable (P b)) :
    PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun b => @decide (P b) (d b))

register_information_template indexedDecision

private def decisionTypeRetained : TemplateAudit.PlanNode → Bool
  | .app (.app (.atom (.const ``decide _)) proposition) _ =>
    match proposition with | .typeNode _ => true | _ => false
  | .app f a => decisionTypeRetained f || decisionTypeRetained a
  | .audit input body => decisionTypeRetained input || decisionTypeRetained body
  | .lam t b _ | .forallE t b _ => decisionTypeRetained t || decisionTypeRetained b
  | .letE t v b _ => decisionTypeRetained t || decisionTypeRetained v || decisionTypeRetained b
  | .expanded _ b | .typeNode b | .mdata _ b | .proj _ _ b => decisionTypeRetained b
  | _ => false

def targetArena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool (Fin 1)
  Law _ := Nat.lt 0 (Nat.succ 0)

def independentArena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool (Fin 1)
  Law _ := Nat.lt 1 (Nat.succ 1)

instance : DecidableEq targetArena.State := instDecidableEqBool
instance : DecidableEq independentArena.State := instDecidableEqBool

information_theorem target in targetArena primitives (boundTemplate 0)
  : Nat.lt 0 (Nat.succ 0) := Nat.zero_lt_succ 0

information_theorem independent in independentArena primitives (boundTemplate 0)
  : Nat.lt 1 (Nat.succ 1) := Nat.lt_succ_self 1

run_meta do
  let .ok decisionPlan := TemplateAudit.selectedPlan (← getEnv) ``indexedDecision
    | throwError "setup: missing indexed decision template"
  logInfo m!"[{if decisionTypeRetained decisionPlan.plan then "PASS" else "FAIL"}] decision_proposition_type_retained"
  let .ok plan := TemplateAudit.selectedPlan (← getEnv) ``boundTemplate
    | throwError "setup: missing checked template"
  let retained := (plan.dependencies.find? (·.name == ``boundProof)).any fun input =>
    !input.typeIdentity.isEmpty && input.bodyIdentity.isEmpty
  logInfo m!"[{if retained then "PASS" else "FAIL"}] enrollment_proof_input_retained"
  for (name, label, shouldValidate) in #[
      (``target, "instantiated_proof_type_target_rejected", false),
      (``independent, "instantiated_independent_proof_type_accepted", true)] do
    let some event := (TemplateBinding.inventory (← getEnv)).find? (·.key.theoremName == name)
      | throwError "setup: missing native registration"
    let descriptor ← mkAppM ``boundTemplate #[mkNatLit 0]
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

end LeanInformationAudit.Tests.DeclaredObligations
