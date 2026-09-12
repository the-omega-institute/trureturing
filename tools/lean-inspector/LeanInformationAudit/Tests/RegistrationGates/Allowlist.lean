import LeanInformationAudit.Tests.RegistrationGates.ProvenanceTypes

open Lean LeanInformationAudit
namespace RegistrationProvenance

noncomputable def directClassicalRead (_ : Unit) (x : Bool) : Bool :=
  if @decide specificStatement (Classical.propDecidable specificStatement) then x else false
check_provenance "ClassicalDirect" using directClassicalRead expects "unclassified_form" for specificTruth

def ctorDecisionRead (_ : Unit) (x : Bool) : Bool :=
  if @decide specificStatement (.isTrue specificTruth) then x else false
check_provenance "CtorDecisionOfStatement" using ctorDecisionRead expects "forbidden_dependency" for specificTruth

noncomputable def closedDecisionRead (_ : Unit) (x : Bool) : Bool :=
  if @decide theoremProposition (Classical.propDecidable theoremProposition) then x else false
check_provenance "ClosedDecisionProtected" using closedDecisionRead expects "unclassified_form" for specificTruth

end RegistrationProvenance
