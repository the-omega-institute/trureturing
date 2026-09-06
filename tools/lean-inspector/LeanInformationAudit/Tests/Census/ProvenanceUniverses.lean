import LeanInformationAudit.Tests.Census.CommandRejection

open Lean LeanInformationAudit DispositionCensus Lean.Elab.Command
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.ProvenanceUniverses

universe u

def arena : StructuralArena.{u} := ⟨ULift.{u} Nat⟩

def law : StructuralPrimitiveLawArena arena.{u} where
  signature := ⟨Unit, inferInstance, fun _ => Nat⟩
  Law r := ∀ n, r.readout () n < 2

def readouts : StructuralPrimitiveRealization arena.{u} law.signature :=
  ⟨fun _ n => n.down % 2⟩

theorem nondegenerate : law.{u}.Nondegenerate := by
  refine ⟨readouts, ⟨fun _ _ => (2 : Nat)⟩, fun n => Nat.mod_lt n.down (by decide), ?_⟩
  intro h
  exact Nat.lt_irrefl 2 (h ⟨0⟩)

structural_theorem generated in law realization readouts nondegeneracy nondegenerate :=
  fun n => Nat.mod_lt n.down (by decide)

def testCatalog : StructuralCatalog arena.{u} :=
  ⟨Unit, inferInstance, inferInstance, fun _ => generated.__structural_unit⟩

theorem registration : StructuralRegistrationEvidence ``generated arena.{u}
    generated.__structural_unit testCatalog () (law.{u}.Law readouts) := ⟨rfl, rfl⟩

def witness : StructuralStrictnessCertificate testCatalog.{u} () where
  inclusion := by intro _ _ _ i ne; exact (ne rfl).elim
  left := ⟨0⟩
  right := ⟨1⟩
  without_agrees := by intro i ne; exact (ne rfl).elim
  full_separates := by
    intro full
    exact Nat.zero_ne_one (full () (Set.mem_univ ()) ())

theorem strictness : testCatalog.{u}.StructurallyLowersEscape () :=
  testCatalog.structurallyLowersEscape_of_certificate () witness

def inventory : DispositionInventory := ⟨"universe-head", #[
  ⟨⟨``generated, "universe-id"⟩, .structuralOccurrence {
    canonicalArena := ``arena
    registration := ``registration
    «realization» := ``generated.__structural_realization
    strictnessCertificate := ``strictness
    witnessCertificate := ``witness }⟩]⟩

/-- info: accepted=true structural=1 certificate-kernel-checked=true -/
#guard_msgs in
run_cmd do
  unless !(← getConstInfo ``generated).levelParams.isEmpty do
    throwError "expected a universe-polymorphic generated theorem"
  expectAcceptedCensus (← getEnv).header.mainModule ``inventory `coverage inventory 1

#print axioms generated
#print axioms nondegenerate
#print axioms coverage

end LeanInformationAudit.Tests.Census.ProvenanceUniverses
