import LeanInformationAudit.DispositionCensus
import LeanInformationAudit.Tests.SealSuccess

open Lean LeanInformationAudit DispositionCensus
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.Evidence

def finiteStates : Arena.StateEnumeration SealSuccess.t001Arena.toArena where
  states := [false, true]
  nodup := by change ([false, true] : List Bool).Nodup; decide
  complete := by change ([false, true] : List Bool).toFinset = Finset.univ; decide

theorem finiteNondegenerate : SealSuccess.t001Arena.toArena.Nondegenerate := by decide

abbrev infiniteArena : StructuralArena where
  State := Nat

def structuralLawArena : StructuralPrimitiveLawArena infiniteArena where
  signature := ⟨Unit, inferInstance, fun _ => Nat⟩
  Law readouts := ∀ n, readouts.readout () n < 2

def structuralReadouts : StructuralPrimitiveRealization infiniteArena structuralLawArena.signature :=
  ⟨fun _ n => n % 2⟩

theorem structuralLawNondegenerate : structuralLawArena.Nondegenerate := by
  refine ⟨structuralReadouts, ⟨fun _ _ => (2 : Nat)⟩,
    fun n => Nat.mod_lt n (by decide), ?_⟩
  intro holds
  exact (Nat.lt_irrefl 2) (holds 0)

structural_theorem structuralTheorem in structuralLawArena
  realization structuralReadouts nondegeneracy structuralLawNondegenerate :=
  fun n => Nat.mod_lt n (by decide)

def structuralCatalog : StructuralCatalog infiniteArena where
  Index := Unit
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  theoremAt := fun _ => structuralTheorem.__structural_unit

theorem structuralRegistration : StructuralRegistrationEvidence ``structuralTheorem
    infiniteArena structuralTheorem.__structural_unit
    structuralCatalog () (∀ n : Nat, n % 2 < 2) := ⟨rfl, rfl⟩

def structuralWitness : StructuralStrictnessCertificate structuralCatalog () where
  inclusion := by
    intro _ _ _ candidate candidateNe
    exact (candidateNe rfl).elim
  left := 0
  right := 1
  without_agrees := by
    intro candidate candidateNe
    exact (candidateNe rfl).elim
  full_separates := by
    intro full
    have incompatible := full () (Set.mem_univ ()) ()
    exact Nat.zero_ne_one incompatible

theorem structuralStrictness : structuralCatalog.StructurallyLowersEscape () :=
  structuralCatalog.structurallyLowersEscape_of_certificate () structuralWitness

theorem boundedTheorem : ∀ n : Nat, n + 0 = n := fun _ => rfl

def truncation : BoundedTruncationFamily (∀ n : Nat, n + 0 = n) where
  arena := fun bound => Arena.ofFintype (Fin (bound + 1))
  approximation := fun bound => ∀ n : Nat, n < bound → n + 0 = n
  restrict := fun _ statement n _ => statement n

theorem comparison : (∀ n : Nat, n + 0 = n) → truncation.approximation 12 :=
  truncation.restrict 12

theorem transfer : truncation.approximation 12 → (∀ n : Nat, n + 0 = n) :=
  fun _ => boundedTheorem

theorem closedNumerical : 2 + 3 = 5 := by decide

theorem closedObligation : ClosedNumericalObligation ``closedNumerical (2 + 3) 5 :=
  ⟨closedNumerical⟩

def noCarrier : UnreachableElaborationEvidence (2 + 3 = 5) where
  reason := .noCanonicalObjectCarrier
  candidateArena := none
  explanation := "Closed numerical proposition; no explicit object carrier or primitive realization."
  failedObligation := some ``closedObligation

def inventory : DispositionInventory := {
  headSha := "fixture-head"
  entries := #[
    ⟨⟨``SealSuccess.idTheorem, "finite-id"⟩, .finiteOccurrence {
      canonicalArena := ``SealSuccess.t001Arena
      registration := ``SealSuccess.idTheorem.__information_unit
      «realization» := ``SealSuccess.idTheorem.__primitive_realization
      nondegeneracyCertificate := ``finiteNondegenerate
      stateEnumerationCertificate := ``finiteStates }⟩,
    ⟨⟨``structuralTheorem, "structural-id"⟩, .structuralOccurrence {
      canonicalArena := ``infiniteArena
      registration := ``structuralRegistration
      «realization» := ``structuralTheorem.__structural_realization
      strictnessCertificate := ``structuralStrictness
      witnessCertificate := ``structuralWitness }⟩,
    ⟨⟨``boundedTheorem, "bounded-id"⟩, .boundedFiniteTruncation {
      truncationFamily := ``truncation
      bound := 12
      comparisonStatement := ``comparison
      certification := .reportOnly }⟩,
    ⟨⟨``closedNumerical, "unreachable-id"⟩,
      .unreachable ⟨.noCanonicalObjectCarrier, ``noCarrier⟩⟩]
}

expect_information_occurrence SealSuccess.fstTheorem
  in SealSuccess.arena from "LeanInformationAudit.Tests.SealSuccess"
expect_information_occurrence SealSuccess.sndTheorem
  in SealSuccess.arena from "LeanInformationAudit.Tests.SealSuccess"
expect_information_occurrence SealSuccess.notTheorem
  in SealSuccess.notArena from "LeanInformationAudit.Tests.SealSuccess"
expect_information_occurrence SealSuccess.idTheorem
  in SealSuccess.t001Arena from "LeanInformationAudit.Tests.SealSuccess"

#seal_information_theory

run_cmd Lean.Elab.Command.liftTermElabM do
  validateEvidence (← getEnv).header.mainModule inventory

run_cmd do
  let report : FrozenReport := ⟨inventory.headSha, "fixture-digest", inventory.entries.map (·.1)⟩
  Lean.Elab.Command.liftTermElabM do
    Lean.Meta.checkWithKernel (← coverageProof report inventory)

#print axioms finiteStates
#print axioms finiteNondegenerate
#print axioms infiniteArena
#print axioms structuralTheorem
#print axioms structuralLawNondegenerate
#print axioms structuralTheorem.__structural_unit
#print axioms structuralCatalog
#print axioms structuralRegistration
#print axioms structuralTheorem.__structural_realization
#print axioms structuralWitness
#print axioms structuralStrictness
#print axioms boundedTheorem
#print axioms truncation
#print axioms comparison
#print axioms transfer
#print axioms closedNumerical
#print axioms noCarrier
#print axioms inventory

end LeanInformationAudit.Tests.Census.Evidence
