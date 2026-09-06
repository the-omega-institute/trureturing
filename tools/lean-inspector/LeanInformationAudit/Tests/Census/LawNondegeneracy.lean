import LeanInformationAudit.Tests.Census.RegisteredClosedTruth

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.LawNondegeneracy

theorem fakeCertificate : True := True.intro

/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.LawNondegeneracy.fakeGenerated class=structural_occurrence invalid=law.nondegeneracy -/
#guard_msgs in
structural_theorem fakeGenerated in RegisteredClosedTruth.lawArena
  realization RegisteredClosedTruth.readouts nondegeneracy fakeCertificate := rfl

/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.LawNondegeneracy.wrongLawGenerated class=structural_occurrence invalid=law.nondegeneracy -/
#guard_msgs in
structural_theorem wrongLawGenerated in RegisteredClosedTruth.lawArena
  realization RegisteredClosedTruth.readouts nondegeneracy Evidence.structuralLawNondegenerate := rfl

def numericalLaw : StructuralPrimitiveLawArena RegisteredClosedTruth.arena where
  signature := ⟨Unit, inferInstance, fun _ => Nat⟩
  Law _ := 2 + 3 = 5

theorem numericalLawDegenerate : ¬numericalLaw.Nondegenerate := by
  rintro ⟨_, _, _, fails⟩
  exact fails RegisteredClosedTruth.closedTruth

def falseLawArena : StructuralPrimitiveLawArena RegisteredClosedTruth.arena where
  signature := ⟨Unit, inferInstance, fun _ => Nat⟩
  Law _ := False

theorem falseLawDegenerate : ¬falseLawArena.Nondegenerate := by
  rintro ⟨_, _, holds, _⟩
  exact holds

-- Failed generation must leave no theorem, realization, or unit behind.
run_cmd do
  for name in [`fakeGenerated, `wrongLawGenerated] do
    let name := (← getCurrNamespace) ++ name
    for generated in [name, name.str "__structural_realization", name.str "__structural_unit"] do
      if (← getEnv).contains generated then throwError "failed generation leaked {generated}"

#print axioms fakeCertificate
#print axioms numericalLawDegenerate
#print axioms falseLawDegenerate

end LeanInformationAudit.Tests.Census.LawNondegeneracy
