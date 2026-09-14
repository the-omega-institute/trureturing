import LeanInformationAudit.Tests.RegistrationGates.DeclaredTemplates

namespace LeanInformationAudit.Tests.DeclaredRecursion
open Lean Meta Elab Command TemplateAudit
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

inductive ObjectTree where
  | leaf : Bool → ObjectTree
  | pair : ObjectTree → ObjectTree → ObjectTree

inductive ProofTree : Prop where
  | leaf : ProofTree

noncomputable def supplied {X : Type} (tree : ObjectTree) (f : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun x => ObjectTree.rec (fun b => Bool.and b (f x))
    (fun _ _ left right => Bool.and left right) tree)

noncomputable def descendant {X : Type} (tree : ObjectTree) (f : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun x => ObjectTree.rec (fun b => Bool.and b (f x))
    (fun left _ _ rightResult => Bool.and rightResult
      (ObjectTree.rec (fun b => Bool.and b (f x))
        (fun _ _ a b => Bool.and a b) left)) tree)

noncomputable def constructed {X : Type} (tree : ObjectTree) (f : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun x => ObjectTree.rec (fun b => Bool.and b (f x))
    (fun _ _ left right => Bool.and left right) (.pair tree tree))

noncomputable def unrelated {X : Type} (tree : ObjectTree) (f : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun x => (fun other => ObjectTree.rec (fun b => Bool.and b (f x))
    (fun _ _ left right => Bool.and left right) other) tree)

def indexedDecision {X : Type} (P : X → Prop) [d : ∀ x, Decidable (P x)] :
    PrimitiveRealization (cutSignature X Bool) := cutRealization (fun x => decide (P x))

def zeroArityDecision {X : Type} (P : X → Prop) (x : X) [d : Decidable (P x)]
    (f : X → Bool) : PrimitiveRealization (cutSignature X Bool) := cutRealization f

def staticDecision {X : Type} (d : ∀ _x : X, Decidable True) (f : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) := cutRealization f

def arbitraryInstance {X : Type} [flag : Inhabited X] (f : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) := cutRealization f

elab "observe_constructor_recursion" : command => do
  let cases : Array (String × Name × Array Name × Option String) := #[
    ("supplied_ast_recursion_accepted", ``supplied, #[``ObjectTree], none),
    ("descendant_ast_recursion_accepted", ``descendant, #[``ObjectTree], none),
    ("constructed_ast_recursion_rejected", ``constructed, #[``ObjectTree],
      some "unclassified_form:E4c.structural_descent"),
    ("unrelated_lambda_ast_rejected", ``unrelated, #[``ObjectTree],
      some "unclassified_form:E4c.structural_descent"),
    ("prop_inductive_recursion_rejected", ``supplied, #[``ProofTree],
      some "unclassified_form:E4c.proof_inductive"),
    ("indexed_decision_family_accepted", ``indexedDecision, #[], none),
    ("telescope_zero_arity_decision_rejected", ``zeroArityDecision, #[],
      some "unclassified_form:E1.closed_decision_slot"),
    ("telescope_static_decision_family_rejected", ``staticDecision, #[],
      some "unclassified_form:E1.unindexed_decision_family"),
    ("telescope_arbitrary_instance_rejected", ``arbitraryInstance, #[],
      some "unclassified_form:E1.instance_slot")]
  for (label, name, asts, expected) in cases do
    let saved ← get
    let result ← enroll name asts
    let actual := match result with | .ok () => none | .error text => some text
    let selected := selectedPlan (← getEnv) name
    let retained := selected.isOk
    set saved
    if let .ok plan := selected then
      let .ok bytes := planEncoding plan | throwError "setup: retained recursion plan cannot encode"
      let decoded := PlanDecoder.decode bytes (32 * bytes.size)
      let valid := match decoded with
        | .ok (plan, _) => (planEncoding plan).toOption == some bytes
        | .error _ => false
      logInfo m!"[{if valid then "PASS" else "FAIL"}] recursion_plan_import_{name} bytes={bytes.size} work={plan.chargedWork}"
      if let .error reason := decoded then logInfo m!"actual={reason}"
    logInfo m!"[{if actual == expected && retained == expected.isNone then "PASS" else "FAIL"}] {label} result={repr actual}"

observe_constructor_recursion

end LeanInformationAudit.Tests.DeclaredRecursion
