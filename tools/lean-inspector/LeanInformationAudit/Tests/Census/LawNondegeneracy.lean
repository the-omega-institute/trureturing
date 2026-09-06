import LeanInformationAudit.Tests.Census.RegisteredClosedTruth

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.LawNondegeneracy

theorem fakeCertificate : True := True.intro

-- Restore the environment to keep a mutant acceptance from poisoning later guards.
/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.RegisteredClosedTruth.closedTruth class=structural_occurrence invalid=law.nondegeneracy -/
#guard_msgs in
run_cmd do
  let env ← getEnv
  try
    elabCommand (← `(command|
      register_structural_law RegisteredClosedTruth.registration in RegisteredClosedTruth.lawArena
        nondegeneracy fakeCertificate))
  finally
    setEnv env

/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.RegisteredClosedTruth.closedTruth class=structural_occurrence invalid=law.nondegeneracy -/
#guard_msgs in
run_cmd do
  let env ← getEnv
  try
    elabCommand (← `(command|
      register_structural_law RegisteredClosedTruth.registration in RegisteredClosedTruth.lawArena
        nondegeneracy Evidence.structuralLawNondegenerate))
  finally
    setEnv env

/--
info: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.RegisteredClosedTruth.closedTruth class=structural_occurrence invalid=realization.law_registration
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  expectRejectedCensus (← getEnv).header.mainModule ``RegisteredClosedTruth.inventory
    `rejectedRegistrationCoverage RegisteredClosedTruth.inventory
    (classError ``RegisteredClosedTruth.closedTruth "structural_occurrence"
      "realization.law_registration")

-- Corrupt only inspector metadata, via its resolved private declaration. This
-- exercises persisted-entry validation without exposing a production bypass.
/--
info: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.RegisteredClosedTruth.closedTruth class=structural_occurrence invalid=realization.law_nondegeneracy
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  let env ← getEnv
  let some (registryName, _) := env.constants.toList.find? (fun (name, _) =>
      privateToUserName? name == some `LeanInformationAudit.DispositionCensus.structuralLawRegistry)
    | throwError "private structural registry not found"
  let registryId := mkIdent registryName
  try
    elabCommand (← `(command| run_cmd
      modifyEnv fun current => ($registryId).addEntry current
        (``RegisteredClosedTruth.registration, ``RegisteredClosedTruth.lawArena,
          ``fakeCertificate, current.header.mainModule)))
    expectRejectedCensus (← getEnv).header.mainModule ``RegisteredClosedTruth.inventory
      `corruptedRegistrationCoverage RegisteredClosedTruth.inventory
      (classError ``RegisteredClosedTruth.closedTruth "structural_occurrence"
        "realization.law_nondegeneracy")
  finally
    setEnv env

theorem numericalLawDegenerate : ¬RegisteredClosedTruth.lawArena.Nondegenerate := by
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
