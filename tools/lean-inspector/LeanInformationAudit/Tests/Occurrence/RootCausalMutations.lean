import LeanInformationAudit.Tests.Occurrence.RootCausalFixture

open Lean Lean.Elab.Command LeanInformationAudit
open LeanInformationAudit.Tests.RootCausalFixture

namespace LeanInformationAudit.Tests.RootCausalMutations

private def rejectsCausalMutation (second extra : Bool) (label : String)
    (missing unexpected : Array String) : CommandElabM Unit := do
  let original ← getEnv
  try
    registerCausalFixture second extra
    modifyEnv (·.setMainModule designatedInformationRootId)
    let env ← getEnv
    let expected := (expectedOccurrencesForRoot env designatedInformationRootId).map
      (fun row => row.objectArenaName.toString ++ "/" ++ row.theoremName.toString)
      |>.qsort (· < ·)
    let actual := (InformationRegistry.entries env).map (·.occurrenceKeyString)
      |>.qsort (· < ·)
    unless expected.size == 13 &&
        expected.filter (fun key => !actual.contains key) == missing &&
        actual.filter (fun key => !expected.contains key) == unexpected do
      throwError "{label}: wrong mutation input"
    let message ← try
      elabCommand (← `(command| #seal_information_theory))
      pure "accepted"
    catch error =>
      error.toMessageData.toString
    let wanted := s!"IE-C028 AnalysisCertificateMismatch root={designatedInformationRootId} " ++
      "catalog=registry-snapshot component=member-set " ++
      s!"expected={(toJson expected).compress} actual={(toJson actual).compress}"
    unless message == wanted do
      throwError "{label}: wrong failure: {message}"
    unless (SealRecords.forRoot (← getEnv) designatedInformationRootId).isEmpty do
      throwError "{label}: failed seal published records"
    logInfo s!"{label}: IE-C028 missing={(toJson missing).compress} unexpected={(toJson unexpected).compress}"
  finally
    setEnv original

run_cmd rejectsCausalMutation false false "ROOT-B-causal-missing"
  #["D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment.unifiedArena/" ++
    "D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation." ++
    "intervention_strictly_weaker_than_counterfactual"] #[]

run_cmd rejectsCausalMutation true true "ROOT-B-causal-unexpected" #[]
  #["D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment.unifiedArena/" ++
    "LeanInformationAudit.Tests.RootCausalFixture.extraCausalTheorem"]

end LeanInformationAudit.Tests.RootCausalMutations
