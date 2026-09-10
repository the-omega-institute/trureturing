import LeanInformationAudit.Tests.Census.CommandRejection

open Lean LeanInformationAudit DispositionCensus Lean.Elab.Command

namespace LeanInformationAudit.Tests.Census.AssessmentCommand

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def structuralKey : StatementKey := ⟨``Evidence.structuralTheorem, "sha256:0000000000000000000000000000000000000000000000000000000000000029"⟩

def observation (env : Environment) (key : StatementKey) : AnalysisObservation key where
  owningModule := `LeanInformationAudit.Tests.Census.Evidence
  root := env.header.mainModule
  importScope := { modules := env.header.moduleNames.push env.header.mainModule, completed := true }
  queryCompleted := true
  candidates := #[]
  note := ""

/-- Compile the supplied fixture value through the same strict JSON projection. -/
def declareInventory (name : Name) (inventory : DispositionInventory) : CommandElabM Unit := do
  let bytes := Syntax.mkStrLit (toJson inventory).compress
  elabCommand (← `(command| def $(mkIdent (`_root_ ++ name)) : DispositionInventory :=
    match Json.parse $bytes with
    | .error _ => ⟨"invalid-json", #[]⟩
    | .ok json => match DispositionCensus.parseInventory json with
      | .error _ => ⟨"invalid-inventory", #[]⟩
      | .ok value => value))

def expectCase (caseName : Name) (root : Name) (inventory : DispositionInventory)
    (expected : String) (transformReport : Json → Json := id) : CommandElabM Unit := do
  let inventoryName := (← getCurrNamespace) ++ caseName.str "inventory"
  declareInventory inventoryName inventory
  try
    expectRejectedCensus root inventoryName caseName inventory expected transformReport
  catch error => throwError "{caseName}: {error.toMessageData}"

run_cmd do
  let env ← getEnv
  let first : StatementKey := ⟨``Evidence.finiteNondegenerate, "sha256:0000000000000000000000000000000000000000000000000000000000000017"⟩
  let second : StatementKey := ⟨``Evidence.transfer, "sha256:0000000000000000000000000000000000000000000000000000000000000027"⟩
  let inventory : DispositionInventory := ⟨"fixture-head", #[
    Evidence.inventory.entries[2]!, Evidence.inventory.entries[3]!,
    ⟨structuralKey, .observed { observation env structuralKey with candidates := #[
      ``Evidence.structuralRegistration, ``Evidence.structuralTheorem.__structural_realization] }⟩,
    ⟨first, .observed (observation env first)⟩,
    ⟨second, .observed (observation env second)⟩]⟩
  let name := (← getCurrNamespace) ++ `mixedInventory
  declareInventory name inventory
  expectAcceptedCensus env.header.mainModule name `mixedAssessment inventory 0
    (some (5, 2, 3, false))
  logInfo "mixedAssessment accounted=5 certified=2 observed=3 certified_complete=false"

run_cmd do
  let inventory : DispositionInventory :=
    ⟨"fixture-head", #[Evidence.inventory.entries[2]!, Evidence.inventory.entries[3]!]⟩
  let name := (← getCurrNamespace) ++ `certifiedInventory
  declareInventory name inventory
  expectAcceptedCensus (← getEnv).header.mainModule name `allCertified inventory 0
    (some (2, 2, 0, true))
  logInfo "allCertified accounted=2 certified=2 observed=0 certified_complete=true"

run_cmd do
  let env ← getEnv
  let value := { observation env structuralKey with queryCompleted := false }
  expectCase `queryIncompleteRejected env.header.mainModule
    ⟨"fixture-head", #[⟨structuralKey, .observed value⟩]⟩
    (censusError "fixture-head" "query_completed" "true" "false")

run_cmd do
  let env ← getEnv
  let value := { observation env structuralKey with root := `OtherRoot }
  expectCase `observationRootMismatch env.header.mainModule
    ⟨"fixture-head", #[⟨structuralKey, .observed value⟩]⟩
    (censusError "fixture-head" "root" env.header.mainModule.toString "OtherRoot")

run_cmd do
  let env ← getEnv
  let value := { observation env structuralKey with
    importScope := { modules := env.header.moduleNames, completed := true } }
  expectCase `observationScopeMismatch env.header.mainModule
    ⟨"fixture-head", #[⟨structuralKey, .observed value⟩]⟩
    (censusError "fixture-head" "import_scope" "root-import-closure" "module-set-mismatch")

run_cmd do
  let env ← getEnv
  let base := observation env structuralKey
  let value := { base with importScope := { base.importScope with completed := false } }
  expectCase `scopeIncompleteRejected env.header.mainModule
    ⟨"fixture-head", #[⟨structuralKey, .observed value⟩]⟩
    (censusError "fixture-head" "import_scope" "completed" "false")

run_cmd do
  let env ← getEnv
  let base := observation env structuralKey
  let value := { base with importScope := {
    base.importScope with modules := base.importScope.modules.push env.header.mainModule } }
  expectCase `duplicateScopeModuleRejected env.header.mainModule
    ⟨"fixture-head", #[⟨structuralKey, .observed value⟩]⟩
    (censusError "fixture-head" "import_scope" "root-import-closure" "module-set-mismatch")

run_cmd do
  let env ← getEnv
  let value := { observation env structuralKey with owningModule := env.header.mainModule }
  expectCase `owningModuleMismatch env.header.mainModule
    ⟨"fixture-head", #[⟨structuralKey, .observed value⟩]⟩
    (censusError "fixture-head" "owning_module" "LeanInformationAudit.Tests.Census.Evidence"
      env.header.mainModule.toString)

run_cmd do
  let env ← getEnv
  for (caseName, candidate) in [(`unknownCandidateRejected, `MissingRealization),
      (`unrelatedCandidateRejected, ``Evidence.transfer)] do
    let value := { observation env structuralKey with candidates := #[candidate] }
    expectCase caseName env.header.mainModule
      ⟨"fixture-head", #[⟨structuralKey, .observed value⟩]⟩
      (censusError "fixture-head" "candidates" "matching-registration-or-realization"
        candidate.toString)

run_cmd do
  let env ← getEnv
  let inventory : DispositionInventory := ⟨"fixture-head", #[Evidence.inventory.entries[1]!,
    ⟨structuralKey, .observed (observation env structuralKey)⟩]⟩
  expectCase `certifiedObservedDuplicate env.header.mainModule inventory
    s!"IE-C035 DuplicateAnalysisDisposition theorem={structuralKey.theoremName} \
statement_id=sha256:0000000000000000000000000000000000000000000000000000000000000029 records=[0,1]" fun report =>
      let declarations := Json.arr #[Json.mkObj [("kind", toJson "theorem"),
        ("declaration_name_key", toJson (encodeNameKey structuralKey.theoremName)),
        ("statement_id", toJson "sha256:0000000000000000000000000000000000000000000000000000000000000029")]]
      report.setObjVal! "nodes" (Json.arr #[Json.mkObj [
        ("freeze_status", toJson "frozen"), ("declarations", declarations)]])

def elaborationObservation : AnalysisObservation structuralKey where
  owningModule := `LeanInformationAudit.Tests.Census.Evidence
  root := `LeanInformationAudit.Tests.Census.AssessmentCommand
  importScope := ⟨#[], true⟩
  queryCompleted := true
  candidates := #[]
  note := "No mathematical impossibility claim."

run_cmd do
  let inventory : DispositionInventory := ⟨"fixture-head", #[⟨structuralKey,
    .certified <| .unreachable ⟨.noCanonicalObjectCarrier, ``elaborationObservation⟩⟩]⟩
  expectCase `observationAsUnreachableRejected (← getEnv).header.mainModule inventory
    (classError structuralKey.theoremName "unreachable" "evidence")

end LeanInformationAudit.Tests.Census.AssessmentCommand
