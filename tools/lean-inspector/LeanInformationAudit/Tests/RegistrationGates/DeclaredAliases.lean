import LeanInformationAudit.Tests.RegistrationGates.DeclaredTemplates

namespace LeanInformationAudit.Tests.DeclaredAliases
open Lean Meta Elab Command TemplateAudit
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

def predicateFamily {X : Type} (P : X → Prop) [DecidablePred P] :
    PrimitiveRealization (cutSignature X Bool) := cutRealization (fun x => decide (P x))

def relationFamily {X : Type} (P : X → X → Prop) [DecidableRel P] :
    PrimitiveRealization (cutSignature X Bool) := cutRealization (fun x => decide (P x x))

def staticPredicate [DecidablePred (fun _ : Bool => True)] :
    PrimitiveRealization (cutSignature Bool Bool) := cutRealization (fun b => b)

def staticRelation [DecidableRel (fun _ _ : Bool => True)] :
    PrimitiveRealization (cutSignature Bool Bool) := cutRealization (fun b => b)

def discardedIndex (d : ∀ x : Bool, Decidable ((fun _ : Bool => True) x)) :
    PrimitiveRealization (cutSignature Bool Bool) := cutRealization (fun b => b)

def closedAlias : Prop := True

def hiddenProposition {X : Type} (f : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) :=
  let independent : closedAlias := True.intro
  cutRealization f

def fixedProposition {X : Type} (f : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) :=
  let independent : True := True.intro
  cutRealization f

def proofFamily {X : Type} (P : X → Prop) (_h : ∀ x, P x) (f : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) := cutRealization f

elab "observe_template_alias_boundaries" : command => do
  let cases : Array (String × Name × Option String) := #[
    ("indexed_decidable_pred_alias_accepted", ``predicateFamily, none),
    ("indexed_decidable_rel_alias_accepted", ``relationFamily, none),
    ("static_decidable_pred_alias_rejected", ``staticPredicate,
      some "unclassified_form:E1.unindexed_decision_family"),
    ("static_decidable_rel_alias_rejected", ``staticRelation,
      some "unclassified_form:E1.unindexed_decision_family"),
    ("discarded_decision_index_rejected", ``discardedIndex,
      some "unclassified_form:E1.unindexed_decision_family"),
    ("closed_proposition_alias_rejected", ``hiddenProposition,
      some "unclassified_form:E2.closed_proposition"),
    ("independent_fixed_proof_leaf_accepted", ``fixedProposition, none)]
  for (label, name, expected) in cases do
    let saved ← get
    let result ← enroll name
    let actual := match result with | .ok () => none | .error message => some message
    let present := (selectedPlan (← getEnv) name).isOk
    set saved
    (if actual == expected && present == expected.isNone then logInfo else logError) m!"[{if actual == expected && present == expected.isNone then "PASS" else "FAIL"}] {label} result={repr actual}"

observe_template_alias_boundaries

run_cmd do
  let saved ← get
  let .ok () ← enroll ``proofFamily | throwError "setup: proof family enrollment failed"
  let .ok plan := selectedPlan (← getEnv) ``proofFamily
    | throwError "setup: proof family plan absent"
  let valid := plan.slots[2]?.map (·.kind) == some SlotKind.proof
  set saved
  (if valid then logInfo else logError) m!"[{if valid then "PASS" else "FAIL"}] quantified_proof_slot_retained_as_proof"

end LeanInformationAudit.Tests.DeclaredAliases
