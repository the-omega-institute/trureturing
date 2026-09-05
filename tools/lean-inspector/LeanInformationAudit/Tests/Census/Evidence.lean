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

theorem structuralTheorem : ∀ n : Nat, n % 2 < 2 := fun n => Nat.mod_lt n (by decide)

def structuralUnit : StructuralTheoremUnit infiniteArena where
  PrimitiveIndex := Unit
  primitiveIndexFintype := inferInstance
  primitiveKernel := fun _ => {
    relation := fun left right => left % 2 = right % 2
    equivalence := eq_equivalence.comap fun state => state % 2 }
  Statement := ∀ n : Nat, n % 2 < 2
  proof := structuralTheorem

def structuralCatalog : StructuralCatalog infiniteArena where
  Index := Unit
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  theoremAt := fun _ => structuralUnit

theorem structuralRegistration : StructuralRegistrationEvidence ``structuralTheorem
    infiniteArena structuralUnit
    structuralCatalog () (∀ n : Nat, n % 2 < 2) := ⟨rfl, rfl⟩

theorem structuralRealization : structuralUnit.Statement = (∀ n : Nat, n % 2 < 2) := rfl

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

def noCarrier : UnreachableElaborationEvidence (2 + 3 = 5) where
  reason := .noCanonicalObjectCarrier
  candidateArena := none
  explanation := "Closed numerical proposition; no explicit object carrier or primitive realization."

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
      «realization» := ``structuralRealization
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

run_cmd Lean.Elab.Command.liftTermElabM do
  validateEvidence `LeanInformationAudit.Tests.SealSuccess inventory

run_cmd do
  let report : FrozenReport := ⟨inventory.headSha, "fixture-digest", inventory.entries.map (·.1)⟩
  Lean.Elab.Command.liftTermElabM do
    Lean.Meta.checkWithKernel (← coverageProof report inventory)

#print axioms finiteStates
#print axioms finiteNondegenerate
#print axioms infiniteArena
#print axioms structuralTheorem
#print axioms structuralUnit
#print axioms structuralCatalog
#print axioms structuralRegistration
#print axioms structuralRealization
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
