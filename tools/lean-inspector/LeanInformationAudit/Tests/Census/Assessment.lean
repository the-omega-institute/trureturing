import LeanInformationAudit.Tests.Census.Json

open Lean LeanInformationAudit DispositionCensus

namespace LeanInformationAudit.Tests.Census.Assessment

def rejected {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

def observation (key : StatementKey) : AnalysisObservation key where
  owningModule := `Fixture
  root := `Fixture
  importScope := { modules := #[`Fixture], completed := true }
  queryCompleted := true
  candidates := #[]
  note := "No certification recorded."

def observedRow (name : Name) (id : String) :
    Sigma fun key : StatementKey => CensusAssessment key :=
  let key := StatementKey.mk name id
  ⟨key, .observed (observation key)⟩

def mixed : DispositionInventory := ⟨"fixture-head", #[
  fourRows.entries[0]!, fourRows.entries[1]!,
  observedRow `Fixture.first "sha256:0000000000000000000000000000000000000000000000000000000000000016", observedRow `Fixture.second "sha256:0000000000000000000000000000000000000000000000000000000000000026",
  observedRow `Fixture.third "sha256:000000000000000000000000000000000000000000000000000000000000002b"]⟩

def mixedReport : FrozenReport := ⟨mixed.headSha, "fixture-digest", mixed.keys.toArray⟩

def mixedCounts : Except String Bool := do
  let result ← artifact mixedReport mixed
  let counts ← result.getObjVal? "counts"
  return (← counts.getObjValAs? Nat "accounted") == 5 &&
    (← counts.getObjValAs? Nat "certified") == 2 &&
    (← counts.getObjValAs? Nat "observed") == 3 &&
    (← counts.getObjValAs? Nat "observed_query_completed") == 3 &&
    (← counts.getObjValAs? Nat "observed_query_incomplete") == 0 &&
    (← counts.getObjValAs? Nat "finite_occurrence") == 1 &&
    (← counts.getObjValAs? Nat "structural_occurrence") == 1 &&
    (← counts.getObjValAs? Nat "bounded_finite_truncation") == 0 &&
    (← counts.getObjValAs? Nat "unreachable") == 0 &&
    (← counts.getObjValAs? Nat "no_canonical_object_carrier") == 0 &&
    (← counts.getObjValAs? Nat "no_finite_primitive_bundle") == 0 &&
    (← counts.getObjValAs? Nat "no_faithful_primitive_realization") == 0 &&
    !(← result.getObjValAs? Bool "certified_complete")

run_cmd unless mixedCounts == .ok true do throwError "mixedCounts"
run_cmd unless mixed.certifiedKeys == [fourRows.entries[0]!.1, fourRows.entries[1]!.1] do
  throwError "certifiedKeys"

def allCertifiedComplete : Except String Bool := do
  let result ← artifact report fourRows
  result.getObjValAs? Bool "certified_complete"

run_cmd unless allCertifiedComplete == .ok true do throwError "allCertifiedComplete"
run_cmd unless parseInventory (toJson mixed) == .ok { mixed with entries := mixed.sortedEntries } do
  throwError "assessmentRoundtrip"

def incompleteQuery : DispositionInventory := ⟨"fixture-head", #[
  ⟨⟨`Fixture.first, "sha256:0000000000000000000000000000000000000000000000000000000000000016"⟩, .observed {
    observation ⟨`Fixture.first, "sha256:0000000000000000000000000000000000000000000000000000000000000016"⟩ with queryCompleted := false }⟩]⟩

def incompleteQueryRejected : Bool :=
  rejected (artifact ⟨"fixture-head", "digest", incompleteQuery.keys.toArray⟩ incompleteQuery)

run_cmd unless incompleteQueryRejected do throwError "incompleteQueryRejected"

def incompleteScope : DispositionInventory := ⟨"fixture-head", #[
  ⟨⟨`Fixture.first, "sha256:0000000000000000000000000000000000000000000000000000000000000016"⟩, .observed {
    observation ⟨`Fixture.first, "sha256:0000000000000000000000000000000000000000000000000000000000000016"⟩ with
      importScope := { modules := #[`Fixture], completed := false } }⟩]⟩

def incompleteScopeRejected : Bool :=
  rejected (artifact ⟨"fixture-head", "digest", incompleteScope.keys.toArray⟩ incompleteScope)

run_cmd unless incompleteScopeRejected do throwError "incompleteScopeRejected"

def censusContainerAccepted : Except String Unit := do
  validateAnalysisInventory `Fixture (← artifact mixedReport mixed)

run_cmd unless censusContainerAccepted == .ok () do throwError "censusContainerAccepted"

def extraArtifactFieldRejected : Except String Bool := do
  let result ← artifact mixedReport mixed
  return rejected (checkArtifact mixedReport mixed (result.setObjVal! "extra" (toJson true)))

run_cmd unless extraArtifactFieldRejected == .ok true do throwError "extraArtifactFieldRejected"

def extraCountFieldRejected : Except String Bool := do
  let result ← artifact mixedReport mixed
  let counts ← result.getObjVal? "counts"
  return rejected (validateAnalysisInventory `Fixture (result.setObjVal! "counts"
    (counts.setObjVal! "extra_status" (toJson (0 : Nat)))))

run_cmd unless extraCountFieldRejected == .ok true do throwError "extraCountFieldRejected"

private def withoutField (value : Json) (field : String) : Json :=
  match value.getObj? with
  | .error _ => value
  | .ok fields => Json.mkObj (fields.toArray.toList.filter (·.1 != field))

def closedContainerCases : Except String Unit := do
  let result ← artifact mixedReport mixed
  let counts ← result.getObjVal? "counts"
  let check (name : String) (candidate : Json) : Except String Unit := do
    unless rejected (validateAnalysisInventory `Fixture candidate) do throw name
  for field in censusArtifactFields do
    check s!"missingRootField:{field}" (withoutField result field)
  for (field, _) in (count mixed).fields do
    check s!"missingCountField:{field}" (result.setObjVal! "counts" (withoutField counts field))
  check "forgedCompleteness" (result.setObjVal! "certified_complete" (toJson true))
  check "forgedObservedCount" (result.setObjVal! "counts"
    (counts.setObjVal! "observed" (toJson (0 : Nat))))
  check "extraSourceField" (result.setObjVal! "source_inputs" (Json.arr #[Json.mkObj [
    ("module", toJson "Fixture"), ("path", toJson "Fixture.lean"),
    ("sha256", toJson "digest"), ("extra", toJson true)]]))
  let rows ← result.getObjValAs? (Array Json) "rows"
  let some row := rows.find? fun row => row.getObjValAs? String "class" == .ok "observed"
    | throw "missing observation fixture"
  let payload ← row.getObjVal? "payload"
  let scope ← payload.getObjVal? "import_scope"
  for (name, changed) in [
      ("extraObservationField", row.setObjVal! "payload" (payload.setObjVal! "evidence" Json.null)),
      ("extraScopeField", row.setObjVal! "payload" (payload.setObjVal! "import_scope"
        (scope.setObjVal! "unqueried" (toJson true)))),
      ("invalidQueryStatus", row.setObjVal! "payload"
        (payload.setObjVal! "query_completed" (toJson "unknown"))),
      ("observationAsUnreachableJson", row.setObjVal! "class" (toJson "unreachable"))] do
    check name (result.setObjVal! "rows" (Json.arr (rows.map fun value =>
      if value == row then changed else value)))

run_cmd do
  if let .error message := closedContainerCases then throwError message

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.Meta.checkWithKernel (← coverageProof mixedReport mixed)

end LeanInformationAudit.Tests.Census.Assessment
