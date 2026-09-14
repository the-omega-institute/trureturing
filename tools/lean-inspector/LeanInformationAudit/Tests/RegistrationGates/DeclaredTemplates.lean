import D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates
import LeanInformationAudit.Syntax

namespace LeanInformationAudit.Tests.DeclaredTemplates
open Lean Meta Elab Command TemplateAudit
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

-- A homogeneous signature avoids proof-to-data Eq.rec transports. The existing
-- heterogeneous separation signature is an explicit unsupported control below.
def symbolicSignature (X Y : Type) [DecidableEq Y] : PrimitiveSignature X where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Y
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def symbolicPointwise {X Y : Type} [DecidableEq Y] (f g : X → Y) :
    PrimitiveRealization (symbolicSignature X Y) where
  readout := fun b x => Bool.rec (f x) (g x) b
  anchor := Fin.elim0

def boolCases {X : Type} (f g : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun x => Bool.rec (f x) (g x) (f x))

def propositionSlot (P : Prop) {X : Type} (f : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) := cutRealization f

def wrongInterface (x : Bool) : Bool := x

def closedDecision {X : Type} : PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun _ => decide True)

def recursiveBody {X : Type} (f : X → Bool) (n : Nat) :
    PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun x => Nat.rec (f x) (fun _ b => b) n)

/-- Each oracle captures the actual enrollment result, then restores the whole
command state. A setup/compiler failure is separate from an expected [FAIL]. -/
elab "observe_declared_template_enrollment" : command => do
  let cases : Array (String × Name × Option String) := #[
    ("symbolic_pointwise_telescope_accepted",
      ``symbolicPointwise, none),
    ("constructive_bool_cases_accepted", ``boolCases, none),
    ("existing_pointwise_eq_cast_is_unsupported",
      `D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.pointwiseEqRealization,
      some "unclassified_form:E4.recursion:Eq.rec"),
    ("telescope_prop_slot_rejected", ``propositionSlot, some "unclassified_form:E1.proposition_slot"),
    ("telescope_wrong_interface_rejected", ``wrongInterface, some "unclassified_form:E1.return_interface"),
    ("body_closed_decision_rejected", ``closedDecision, some "forbidden_dependency:E6.closed_decision"),
    ("body_recursive_definition_rejected", ``recursiveBody, some "unclassified_form:E4.recursion:Nat.rec")]
  for (label, name, expected) in cases do
    let state ← get
    let result ← enroll name
    let actual := match result with | .ok () => none | .error text => some text
    let present := (selectedPlan (← getEnv) name).isOk
    set state
    let ok := actual == expected && present == expected.isNone
    logInfo m!"[{if ok then "PASS" else "FAIL"}] {label} result={repr actual}"

observe_declared_template_enrollment

end LeanInformationAudit.Tests.DeclaredTemplates
