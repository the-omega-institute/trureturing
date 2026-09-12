import LeanInformationAudit.Tests.Census.RegisteredClosedTruth

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.LawNondegeneracy

theorem fakeCertificate : True := True.intro

-- Invalid variation is deferred to the delta consumer, with C048 precedence.
structural_theorem fakeGenerated in RegisteredClosedTruth.lawArena
  realization RegisteredClosedTruth.readouts nondegeneracy fakeCertificate := rfl
structural_theorem wrongLawGenerated in RegisteredClosedTruth.lawArena
  realization RegisteredClosedTruth.readouts nondegeneracy Evidence.structuralLawNondegenerate := rfl

/-- info: IE-C048 -/
#guard_msgs in
run_cmd liftTermElabM do
  for name in [``fakeGenerated, ``wrongLawGenerated] do
    let some entry := (structuralProvenanceEntries (← getEnv)).find? (·.theoremName == name)
      | throwError "missing registration"
    let some message ← RegistrationGates.validateStructural entry
      | throwError "invalid Nondegenerate accepted"
    unless message.endsWith "reason=invalid_witness" do throwError "{message}"
  logInfo "IE-C048"

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

#print axioms fakeCertificate
#print axioms numericalLawDegenerate
#print axioms falseLawDegenerate

end LeanInformationAudit.Tests.Census.LawNondegeneracy
