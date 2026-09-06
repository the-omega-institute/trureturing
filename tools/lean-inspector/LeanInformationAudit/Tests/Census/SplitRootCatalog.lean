import LeanInformationAudit.Tests.Census.Evidence

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.SplitRootCatalog

abbrev arena : StructuralArena := ⟨Nat⟩

theorem parity : ∀ n : Nat, n % 2 < 2 := Evidence.structuralTheorem
theorem truth : True := True.intro

def constantUnit : StructuralTheoremUnit arena where
  PrimitiveIndex := Unit
  primitiveIndexFintype := inferInstance
  primitiveKernel _ := ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩
  Statement := True
  proof := truth

abbrev firstCatalog : StructuralCatalog arena :=
  ⟨Fin 2, inferInstance, inferInstance,
    fun i => if i = 0 then Evidence.structuralUnit else constantUnit⟩

abbrev secondCatalog : StructuralCatalog arena := firstCatalog

theorem firstRegistration : StructuralRegistrationEvidence ``parity arena
    Evidence.structuralUnit firstCatalog 0 (∀ n : Nat, n % 2 < 2) := ⟨rfl, rfl⟩

register_structural_law firstRegistration in Evidence.structuralLawArena
  nondegeneracy Evidence.structuralLawNondegenerate

theorem secondRegistration : StructuralRegistrationEvidence ``truth arena
    constantUnit secondCatalog 1 True := ⟨rfl, rfl⟩

def witness : StructuralStrictnessCertificate firstCatalog 0 where
  inclusion := by intro x y h i _; exact h i (Set.mem_univ i)
  left := 0
  right := 1
  without_agrees := by
    intro i ne p
    fin_cases i
    · exact (ne rfl).elim
    · trivial
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
    ⟨⟨``parity, "parity"⟩, .structuralOccurrence {
      canonicalArena := ``arena
      registration := ``firstRegistration
      «realization» := ``Evidence.structuralRealization
      strictnessCertificate := ``strictness
      witnessCertificate := ``witness }⟩]⟩

end LeanInformationAudit.Tests.Census.SplitRootCatalog
