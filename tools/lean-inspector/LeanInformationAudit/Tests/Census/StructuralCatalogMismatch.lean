import LeanInformationAudit.Tests.Census.Evidence

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command

namespace LeanInformationAudit.Tests.Census.Evidence

theorem duplicateStructuralRegistration : StructuralRegistrationEvidence ``structuralTheorem
    infiniteArena structuralUnit
    structuralCatalog () (∀ n : Nat, n % 2 < 2) := structuralRegistration

-- An imported root is unaffected by registrations outside its own import closure.
/-- info: nominated-root-excludes-caller-peer -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence `LeanInformationAudit.Tests.Census.Evidence inventory
  logInfo "nominated-root-excludes-caller-peer"

/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.Evidence.structuralTheorem class=structural_occurrence invalid=maximal_catalog_membership -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence (← getEnv).header.mainModule { inventory with
    entries := inventory.entries.filter fun row => row.2.className == "structural_occurrence" }

#print axioms duplicateStructuralRegistration

end LeanInformationAudit.Tests.Census.Evidence
