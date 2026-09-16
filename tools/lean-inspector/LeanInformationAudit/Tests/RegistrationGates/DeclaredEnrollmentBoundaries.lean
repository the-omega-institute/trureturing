import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates

namespace LeanInformationAudit.Tests.DeclaredEnrollmentBoundaries
open Lean Meta Elab Command TemplateAudit
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

def boolCases {X : Type} (f g : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun x => Bool.rec (f x) (g x) (f x))

def recursiveBody {X : Type} (f : X → Bool) (n : Nat) :
    PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun x => Nat.rec (f x) (fun _ b => b) n)

def closedDecision {X : Type} : PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun _ => decide True)

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ x : Bool, r.readout () x = x.not.not

instance : DecidableEq arena.State := instDecidableEqBool

information_theorem registeredTruth in arena
  primitives (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm

def registeredCapture {X : Type} (f : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) :=
  (fun (_ : ∀ x : Bool, x = x.not.not) => cutRealization f) registeredTruth

-- The normal companion-name guard must apply before expanding this definition.
def marker.__information_unit : Bool := true

def certificateCapture {X : Type} : PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun _ => marker.__information_unit)

def closedProofType : Prop := True
theorem closedProof : closedProofType := True.intro
theorem independentProof : True := by
  have hidden : closedProofType := closedProof
  exact hidden

-- Both applications accept a True proof. Only the raw argument's inferred type
-- distinguishes these controls; the independent proof implementation is opaque
-- to the provenance boundary and deliberately mentions the forbidden alias.
def forbiddenProofType {X : Type} (f : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) :=
  (fun (_ : True) => cutRealization f) closedProof

def independentProofBody {X : Type} (f : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) :=
  (fun (_ : True) => cutRealization f) independentProof

elab "observe_enrollment_boundaries" : command => do
  let cases : Array (String × Name × Option String) := #[
    ("constructive_bool_cases_accepted", ``boolCases, none),
    ("body_recursive_definition_rejected", ``recursiveBody,
      some "unclassified_form:E4.recursion:Nat.rec"),
    ("body_unknown_eliminator_rejected",
      `D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.pointwiseEqRealization,
      some "unclassified_form:E4.recursion:Eq.rec"),
    ("theorem_agnostic_body_accepted", ``cutRealization, none),
    ("body_registered_truth_rejected", ``registeredCapture,
      some "forbidden_dependency:E6.registered_identity"),
    ("body_closed_decision_rejected", ``closedDecision,
      some "unclassified_form:E3.closed_decision"),
    ("body_certificate_capture_rejected", ``certificateCapture,
      some "forbidden_dependency:E6.registered_identity"),
    ("body_forbidden_proof_type_rejected", ``forbiddenProofType,
      some "unclassified_form:E2.closed_proposition"),
    ("independent_prop_implementation_not_walked", ``independentProofBody, none)]
  for (label, name, expected) in cases do
    let saved ← get
    let result ← enroll name
    let actual := match result with | .ok () => none | .error text => some text
    let present := (selectedPlan (← getEnv) name).isOk
    set saved
    logInfo m!"[{if actual == expected && present == expected.isNone then "PASS" else "FAIL"}] {label} result={repr actual}"

observe_enrollment_boundaries

end LeanInformationAudit.Tests.DeclaredEnrollmentBoundaries
