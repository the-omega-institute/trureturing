import LeanInformationAudit.Tests.RegistrationGates.ProvenanceTypes

open Lean LeanInformationAudit
namespace RegistrationProvenance

noncomputable def directClassicalRead (_ : Unit) (x : Bool) : Bool :=
  if @decide specificStatement (Classical.propDecidable specificStatement) then x else false
check_provenance "ClassicalDirect" using directClassicalRead expects "unclassified_form" for specificTruth

def ctorDecisionRead (_ : Unit) (x : Bool) : Bool :=
  if @decide specificStatement (.isTrue specificTruth) then x else false
check_provenance "CtorDecisionOfStatement" using ctorDecisionRead expects "forbidden_dependency" for specificTruth

def closedDataProp : Prop := (138 : Nat) = 138
def closedDecisionRead (_ : Unit) (x : Bool) : Bool :=
  if @decide closedDataProp (inferInstanceAs (Decidable ((138 : Nat) = 138))) then x else false
check_provenance "ClosedDecisionProtected" using closedDecisionRead expects "unclassified_form" for specificTruth

def closedIndexSignature : D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature :=
  ⟨Unit, inferInstance, fun _ => Bool⟩
def closedTypeRead (_ : Unit) (x : Bool) : Bool :=
  let _ : DecidableEq closedIndexSignature.Index := inferInstanceAs (DecidableEq Unit)
  x
check_provenance "ClosedTypeArgumentAdmitted" using closedTypeRead expects "clean" for specificTruth

def binaryPredicate (a b : Bool) : Prop := a = b
def closedPredicateRead (_ : Unit) (x : Bool) : Bool :=
  let _ := binaryPredicate
  let _ := binaryPredicate true
  x
check_provenance "ClosedPredicateArgumentAdmitted" using closedPredicateRead expects "clean" for specificTruth

end RegistrationProvenance
