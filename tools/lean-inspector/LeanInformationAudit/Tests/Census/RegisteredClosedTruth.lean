import LeanInformationAudit.Tests.Census.CommandRejection

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.RegisteredClosedTruth

abbrev arena : StructuralArena := ⟨Nat⟩
theorem closedTruth : 2 + 3 = 5 := by decide

def lawArena : StructuralPrimitiveLawArena arena where
  signature := ⟨Unit, inferInstance, fun _ => Nat⟩
  Law _ := 2 + 3 = 5

def readouts : StructuralPrimitiveRealization arena lawArena.signature := ⟨fun _ n => n⟩
def unit := readouts.toTheoremUnit (2 + 3 = 5) closedTruth
def testCatalog : StructuralCatalog arena :=
  ⟨Unit, inferInstance, inferInstance, fun _ => unit⟩

theorem registration : StructuralRegistrationEvidence ``closedTruth
    arena unit testCatalog () (2 + 3 = 5) := ⟨rfl, rfl⟩

-- ARCH-C01-residual: registering the constant law itself must fail.
/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.RegisteredClosedTruth.closedTruth class=structural_occurrence invalid=law.nondegeneracy -/
#guard_msgs in
register_structural_law registration in lawArena

theorem bridge : StructuralLegacyPrimitiveRealization lawArena
    (2 + 3 = 5) readouts := ⟨Iff.rfl⟩

def witness : StructuralStrictnessCertificate testCatalog () where
  inclusion := by intro _ _ _ i ne; exact (ne rfl).elim
  left := 0
  right := 1
  without_agrees := by intro i ne; exact (ne rfl).elim
  full_separates := by
    intro full
    exact Nat.zero_ne_one (full () (Set.mem_univ ()) ())

theorem strictness : testCatalog.StructurallyLowersEscape () :=
  testCatalog.structurallyLowersEscape_of_certificate () witness

def inventory : DispositionInventory := ⟨"probe-head", #[
  ⟨⟨``closedTruth, "closed-truth-id"⟩, .structuralOccurrence
    ⟨``arena, ``registration, ``bridge, ``strictness, ``witness⟩⟩]⟩

/--
info: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.RegisteredClosedTruth.closedTruth class=structural_occurrence invalid=realization.law_registration
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  expectRejectedCensus (← getEnv).header.mainModule ``inventory
    `commandCoverage inventory
    (classError ``closedTruth "structural_occurrence" "realization.law_registration")

#print axioms bridge
#print axioms strictness

end LeanInformationAudit.Tests.Census.RegisteredClosedTruth
