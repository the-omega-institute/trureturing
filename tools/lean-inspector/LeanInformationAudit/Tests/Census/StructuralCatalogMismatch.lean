import LeanInformationAudit.Tests.Census.Evidence

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command

namespace LeanInformationAudit.Tests.Census.Evidence

theorem duplicateStructuralRegistration : StructuralRegistrationEvidence infiniteArena structuralUnit
    structuralCatalog () (∀ n : Nat, n % 2 < 2) := structuralRegistration

/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.Evidence.structuralTheorem class=structural_occurrence invalid=maximal_catalog_membership -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence `LeanInformationAudit.Tests.SealSuccess inventory

#print axioms duplicateStructuralRegistration

end LeanInformationAudit.Tests.Census.Evidence
