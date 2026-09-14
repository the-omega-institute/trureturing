import LeanInformationAudit.Tests.Census.Evidence

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.SplitRootCatalog

abbrev arena : StructuralArena := ⟨Nat⟩

def lawArena : StructuralPrimitiveLawArena arena := Evidence.structuralLawArena
theorem nondegenerate : lawArena.Nondegenerate := Evidence.structuralLawNondegenerate
structural_theorem parity in lawArena
  realization Evidence.structuralReadouts nondegeneracy nondegenerate :=
  fun n => Nat.mod_lt n (by decide)
def constantReadouts : StructuralPrimitiveRealization arena lawArena.signature :=
  ⟨fun _ _ => (0 : Nat)⟩
structural_theorem truth in lawArena
  realization constantReadouts nondegeneracy nondegenerate :=
  fun _ => (by decide : (0 : Nat) < 2)

abbrev firstCatalog : StructuralCatalog arena :=
  ⟨Fin 2, inferInstance, inferInstance,
    fun i => if i = 0 then parity.__structural_unit else truth.__structural_unit⟩

abbrev secondCatalog : StructuralCatalog arena := firstCatalog

theorem firstRegistration : StructuralRegistrationEvidence ``parity arena
    parity.__structural_unit firstCatalog 0 (∀ n : Nat, n % 2 < 2) := ⟨rfl, rfl⟩

theorem secondRegistration : StructuralRegistrationEvidence ``truth arena
    truth.__structural_unit secondCatalog 1 (∀ _ : Nat, (0 : Nat) < 2) := ⟨rfl, rfl⟩

def witness : StructuralStrictnessCertificate firstCatalog 0 where
  inclusion := by intro x y h i _; exact h i (Set.mem_univ i)
  left := 0
  right := 1
  without_agrees := by
    intro i ne p
    fin_cases i
    · exact (ne rfl).elim
    · rfl
  full_separates := by
    intro h
    have impossible := h 0 (Set.mem_univ 0) ()
    exact Nat.zero_ne_one impossible

theorem strictness : firstCatalog.StructurallyLowersEscape 0 :=
  firstCatalog.structurallyLowersEscape_of_certificate 0 witness

-- Both indices are present, but their registrations name different catalogs.
/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.SplitRootCatalog.parity class=structural_occurrence invalid=split_canonical_catalog -/
#guard_msgs in
run_cmd liftTermElabM do
  validateEvidence (← getEnv).header.mainModule ⟨"split", #[
    ⟨⟨``parity, "sha256:0000000000000000000000000000000000000000000000000000000000000024"⟩, .certified <| .structuralOccurrence {
      canonicalArena := ``arena
      registration := ``firstRegistration
      «realization» := ``parity.__structural_realization
      strictnessCertificate := ``strictness
      witnessCertificate := ``witness }⟩]⟩

end LeanInformationAudit.Tests.Census.SplitRootCatalog
