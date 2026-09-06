import LeanInformationAudit.Tests.Census.CommandRejection

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.RegisteredClosedTruth

abbrev arena : StructuralArena := ⟨Nat⟩
theorem closedTruth : 2 + 3 = 5 := by decide

def lawArena : StructuralPrimitiveLawArena arena where
  signature := ⟨Unit, inferInstance, fun _ => Nat⟩
  Law r := r.readout () 0 = r.readout () 1

def readouts : StructuralPrimitiveRealization arena lawArena.signature :=
  ⟨fun _ n => n / 2 + 5⟩

theorem nondegenerate : lawArena.Nondegenerate := by
  refine ⟨readouts, ⟨fun _ n => n⟩, rfl, ?_⟩
  exact Nat.zero_ne_one

structural_theorem generated in lawArena realization readouts nondegeneracy nondegenerate := rfl

def testCatalog : StructuralCatalog arena :=
  ⟨Unit, inferInstance, inferInstance, fun _ => generated.__structural_unit⟩

theorem registration : StructuralRegistrationEvidence ``generated
    arena generated.__structural_unit testCatalog () (lawArena.Law readouts) := ⟨rfl, rfl⟩

def witness : StructuralStrictnessCertificate testCatalog () where
  inclusion := by intro _ _ _ i ne; exact (ne rfl).elim
  left := 0
  right := 2
  without_agrees := by intro i ne; exact (ne rfl).elim
  full_separates := by
    intro full
    have impossible := full () (Set.mem_univ ()) ()
    change (5 : Nat) = 6 at impossible
    exact (by decide : (5 : Nat) ≠ 6) impossible

theorem strictness : testCatalog.StructurallyLowersEscape () :=
  testCatalog.structurallyLowersEscape_of_certificate () witness

def positive : DispositionInventory := ⟨"probe-head", #[
  ⟨⟨``generated, "generated-id"⟩, .structuralOccurrence
    ⟨``arena, ``registration, ``generated.__structural_realization, ``strictness, ``witness⟩⟩]⟩

/-- info: accepted=true structural=1 certificate-kernel-checked=true -/
#guard_msgs in
run_cmd do
  expectAcceptedCensus (← getEnv).header.mainModule ``positive `positiveCoverage positive 1

-- Definitional equality does not transfer the generated declaration's provenance.
abbrev closedArena : StructuralArena := arena
def unit := readouts.toTheoremUnit (2 + 3 = 5) closedTruth
def closedCatalog : StructuralCatalog closedArena :=
  ⟨Unit, inferInstance, inferInstance, fun _ => unit⟩
theorem closedRegistration : StructuralRegistrationEvidence ``closedTruth
    closedArena unit closedCatalog () (2 + 3 = 5) := ⟨rfl, rfl⟩
def inventory : DispositionInventory := ⟨"probe-head", #[
  ⟨⟨``closedTruth, "closed-truth-id"⟩, .structuralOccurrence
    ⟨``closedArena, ``closedRegistration, ``generated.__structural_realization,
      ``strictness, ``witness⟩⟩]⟩

/--
info: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.RegisteredClosedTruth.closedTruth class=structural_occurrence invalid=realization.provenance
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  expectRejectedCensus (← getEnv).header.mainModule ``inventory
    `commandCoverage inventory
    (classError ``closedTruth "structural_occurrence" "realization.provenance")

run_cmd liftTermElabM do
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels
      ``closedTruth)) (← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``generated)) do
    throwError "numeric control is not definitionally equal"

#print axioms generated
#print axioms nondegenerate
#print axioms strictness
#print axioms positiveCoverage

end LeanInformationAudit.Tests.Census.RegisteredClosedTruth
