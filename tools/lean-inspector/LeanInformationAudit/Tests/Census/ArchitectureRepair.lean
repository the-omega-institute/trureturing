import LeanInformationAudit.Tests.Census.Evidence

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.ArchitectureRepair

abbrev unrelatedArena : StructuralArena where
  State := Nat

theorem closedTruth : 2 + 3 = 5 := by decide

def unrelatedUnit : StructuralTheoremUnit unrelatedArena where
  PrimitiveIndex := Unit
  primitiveIndexFintype := inferInstance
  primitiveKernel := fun _ => {
    relation := fun left right => left = right
    equivalence := eq_equivalence }
  Statement := 2 + 3 = 5
  proof := closedTruth

def unrelatedCatalog : StructuralCatalog unrelatedArena where
  Index := Unit
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  theoremAt := fun _ => unrelatedUnit

theorem unrelatedRegistration : StructuralRegistrationEvidence ``closedTruth
    unrelatedArena unrelatedUnit unrelatedCatalog () (2 + 3 = 5) := ⟨rfl, rfl⟩

register_structural_law unrelatedRegistration in Evidence.structuralLawArena

theorem unrelatedRealization : unrelatedUnit.Statement = (2 + 3 = 5) := rfl

def unrelatedWitness : StructuralStrictnessCertificate unrelatedCatalog () where
  inclusion := by intro _ _ _ candidate ne; exact (ne rfl).elim
  left := 0
  right := 1
  without_agrees := by intro candidate ne; exact (ne rfl).elim
  full_separates := by
    intro full
    exact Nat.zero_ne_one (full () (Set.mem_univ ()) ())

theorem unrelatedStrictness : unrelatedCatalog.StructurallyLowersEscape () :=
  unrelatedCatalog.structurallyLowersEscape_of_certificate () unrelatedWitness

def unrelatedInventory : DispositionInventory := ⟨"probe-head", #[
  ⟨⟨``closedTruth, "closed-truth-id"⟩, .structuralOccurrence {
    canonicalArena := ``unrelatedArena
    registration := ``unrelatedRegistration
    «realization» := ``unrelatedRealization
    strictnessCertificate := ``unrelatedStrictness
    witnessCertificate := ``unrelatedWitness }⟩]⟩

-- ARCH-C01: statement equality cannot certify compiled primitive kernels.
/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.ArchitectureRepair.closedTruth class=structural_occurrence invalid=realization -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence (← getEnv).header.mainModule unrelatedInventory

theorem wrongKernelTheorem : ∀ n : Nat, n % 2 < 2 := Evidence.structuralTheorem

abbrev wrongKernelArena : StructuralArena := ⟨Nat⟩

def wrongKernelUnit : StructuralTheoremUnit wrongKernelArena := {
  unrelatedUnit with Statement := ∀ n : Nat, n % 2 < 2, proof := wrongKernelTheorem }

def wrongKernelCatalog : StructuralCatalog wrongKernelArena := {
  unrelatedCatalog with theoremAt := fun _ => wrongKernelUnit }

theorem wrongKernelRegistration : StructuralRegistrationEvidence ``wrongKernelTheorem
    wrongKernelArena wrongKernelUnit wrongKernelCatalog () (∀ n : Nat, n % 2 < 2) := ⟨rfl, rfl⟩

register_structural_law wrongKernelRegistration in Evidence.structuralLawArena

def wrongKernelWitness : StructuralStrictnessCertificate wrongKernelCatalog () where
  inclusion := by intro _ _ _ candidate ne; exact (ne rfl).elim
  left := 0
  right := 1
  without_agrees := by intro candidate ne; exact (ne rfl).elim
  full_separates := by
    intro full
    exact Nat.zero_ne_one (full () (Set.mem_univ ()) ())

theorem wrongKernelStrictness : wrongKernelCatalog.StructurallyLowersEscape () :=
  wrongKernelCatalog.structurallyLowersEscape_of_certificate () wrongKernelWitness

/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.ArchitectureRepair.wrongKernelTheorem class=structural_occurrence invalid=realization.compiled_kernels -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence (← getEnv).header.mainModule ⟨"probe-head", #[
    ⟨⟨``wrongKernelTheorem, "wrong-kernel"⟩, .structuralOccurrence {
      canonicalArena := ``wrongKernelArena
      registration := ``wrongKernelRegistration
      «realization» := ``Evidence.structuralRealization
      strictnessCertificate := ``wrongKernelStrictness
      witnessCertificate := ``wrongKernelWitness }⟩]⟩

abbrev wrongLawArena : StructuralArena := ⟨Nat⟩

theorem wrongLawTheorem : 2 + 3 = 5 := closedTruth

def wrongLawUnit : StructuralTheoremUnit wrongLawArena := {
  Evidence.structuralUnit with Statement := 2 + 3 = 5, proof := wrongLawTheorem }

def wrongLawCatalog : StructuralCatalog wrongLawArena := {
  Evidence.structuralCatalog with theoremAt := fun _ => wrongLawUnit }

theorem wrongLawRegistration : StructuralRegistrationEvidence ``wrongLawTheorem
    wrongLawArena wrongLawUnit wrongLawCatalog () (2 + 3 = 5) := ⟨rfl, rfl⟩

register_structural_law wrongLawRegistration in Evidence.structuralLawArena

def wrongLawWitness : StructuralStrictnessCertificate wrongLawCatalog () where
  inclusion := by intro _ _ _ candidate ne; exact (ne rfl).elim
  left := 0
  right := 1
  without_agrees := by intro candidate ne; exact (ne rfl).elim
  full_separates := by
    intro full
    exact Nat.zero_ne_one (full () (Set.mem_univ ()) ())

theorem wrongLawStrictness : wrongLawCatalog.StructurallyLowersEscape () :=
  wrongLawCatalog.structurallyLowersEscape_of_certificate () wrongLawWitness

/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.ArchitectureRepair.wrongLawTheorem class=structural_occurrence invalid=realization.statement -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence (← getEnv).header.mainModule ⟨"probe-head", #[
    ⟨⟨``wrongLawTheorem, "wrong-law"⟩, .structuralOccurrence {
      canonicalArena := ``wrongLawArena
      registration := ``wrongLawRegistration
      «realization» := ``Evidence.structuralRealization
      strictnessCertificate := ``wrongLawStrictness
      witnessCertificate := ``wrongLawWitness }⟩]⟩

-- ARCH-C03: even otherwise valid structural evidence requires a real root.
/-- error: IE-C044 DispositionCensusMismatch head=fixture-head component=root expected=existing-module actual=NoSuchRoot -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence `NoSuchRoot { Evidence.inventory with
    entries := Evidence.inventory.entries.filter fun row =>
      row.2.className == "structural_occurrence" }

/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.Evidence.structuralTheorem class=structural_occurrence invalid=registration.root_membership -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence `LeanInformationAudit.Tests.SealSuccess { Evidence.inventory with
    entries := Evidence.inventory.entries.filter fun row =>
      row.2.className == "structural_occurrence" }

theorem unregisteredDynamics : ∀ n : Nat, n % 2 < 2 :=
  fun n => Nat.mod_lt n (by decide)

def arbitraryNoCarrier : UnreachableElaborationEvidence (∀ n : Nat, n % 2 < 2) :=
  { reason := .noCanonicalObjectCarrier, candidateArena := none, explanation := "x" }

def arbitraryNoBundle : UnreachableElaborationEvidence (∀ n : Nat, n % 2 < 2) :=
  { reason := .noFinitePrimitiveBundle, candidateArena := some ``unrelatedArena, explanation := "x" }

def arbitraryNoRealization : UnreachableElaborationEvidence (∀ n : Nat, n % 2 < 2) :=
  { reason := .noFaithfulPrimitiveRealization, candidateArena := some ``unrelatedArena, explanation := "x" }

-- ARCH-C02: pin each unsupported reason separately.
/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.ArchitectureRepair.unregisteredDynamics class=unreachable invalid=evidence.failed_obligation -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence (← getEnv).header.mainModule ⟨"probe-head", #[
    ⟨⟨``unregisteredDynamics, "id"⟩,
      .unreachable ⟨.noCanonicalObjectCarrier, ``arbitraryNoCarrier⟩⟩]⟩

/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.ArchitectureRepair.unregisteredDynamics class=unreachable invalid=evidence.failed_obligation -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence (← getEnv).header.mainModule ⟨"probe-head", #[
    ⟨⟨``unregisteredDynamics, "id"⟩,
      .unreachable ⟨.noFinitePrimitiveBundle, ``arbitraryNoBundle⟩⟩]⟩

/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.ArchitectureRepair.unregisteredDynamics class=unreachable invalid=evidence.failed_obligation -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence (← getEnv).header.mainModule ⟨"probe-head", #[
    ⟨⟨``unregisteredDynamics, "id"⟩,
      .unreachable ⟨.noFaithfulPrimitiveRealization, ``arbitraryNoRealization⟩⟩]⟩

end LeanInformationAudit.Tests.Census.ArchitectureRepair
