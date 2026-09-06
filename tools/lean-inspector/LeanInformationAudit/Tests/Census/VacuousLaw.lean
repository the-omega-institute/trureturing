import LeanInformationAudit.Tests.Census.ArchitectureRepair
import LeanInformationAudit.Tests.Census.CommandRejection

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.VacuousLaw

def numericalLaw : StructuralPrimitiveLawArena ArchitectureRepair.unrelatedArena where
  signature := ⟨Unit, inferInstance, fun _ => Nat⟩
  Law _ := 2 + 3 = 5

def identityReadouts : StructuralPrimitiveRealization ArchitectureRepair.unrelatedArena
    numericalLaw.signature := ⟨fun _ n => n⟩

theorem numericalBridge : StructuralLegacyPrimitiveRealization numericalLaw
    (2 + 3 = 5) identityReadouts := ⟨Iff.rfl⟩

def numericalInventory : DispositionInventory := {
  ArchitectureRepair.unrelatedInventory with
  entries := ArchitectureRepair.unrelatedInventory.entries.map fun ⟨key, disposition⟩ =>
    ⟨key, match disposition with
      | .structuralOccurrence p => .structuralOccurrence { p with
          «realization» := ``numericalBridge }
      | p => p⟩ }

-- A caller-chosen constant law must not replace the registered object law.
/--
info: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.ArchitectureRepair.closedTruth class=structural_occurrence invalid=realization.canonical_law_arena
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  expectRejectedCensus (← getEnv).header.mainModule ``numericalInventory
    `numericalCoverage numericalInventory
    (classError ``ArchitectureRepair.closedTruth "structural_occurrence"
      "realization.canonical_law_arena")

theorem borrowedBridge : StructuralLegacyPrimitiveRealization Evidence.structuralLawArena
    (2 + 3 = 5) Evidence.structuralReadouts :=
  ⟨⟨fun _ => Evidence.structuralTheorem, fun _ => ArchitectureRepair.closedTruth⟩⟩

def borrowedInventory : DispositionInventory := ⟨"probe-head", #[
  ⟨⟨``ArchitectureRepair.wrongLawTheorem, "borrowed-law"⟩, .structuralOccurrence {
    canonicalArena := ``ArchitectureRepair.wrongLawArena
    registration := ``ArchitectureRepair.wrongLawRegistration
    «realization» := ``borrowedBridge
    strictnessCertificate := ``ArchitectureRepair.wrongLawStrictness
    witnessCertificate := ``ArchitectureRepair.wrongLawWitness }⟩]⟩

-- Even the canonical law cannot attach by an Iff that discards both hypotheses.
/--
info: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.ArchitectureRepair.wrongLawTheorem class=structural_occurrence invalid=realization.object_law
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  expectRejectedCensus (← getEnv).header.mainModule ``borrowedInventory
    `borrowedCoverage borrowedInventory
    (classError ``ArchitectureRepair.wrongLawTheorem "structural_occurrence"
      "realization.object_law")

#print axioms numericalBridge
#print axioms borrowedBridge

end LeanInformationAudit.Tests.Census.VacuousLaw
