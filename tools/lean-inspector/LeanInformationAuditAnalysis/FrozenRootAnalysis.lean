import D5.S3.ConceptDynamics.InformationEscape.InformationRoot
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Projection.FixtureState

/-!
This full-analysis fixture belongs to `LeanInformationAuditAnalysis` and stays
outside every default Lake target because of its cost: approximately 424-528 s
single-module elaboration on a 28-core Apple Silicon host with warm mathlib/project
caches (attempt-1 runs: 528 s / 424 s; measured 2026-09-07).
Build it with `lake build LeanInformationAuditAnalysis` after
`make lean-cache-ensure`. Use `run-analysis-fixtures.sh OUTPUT_DIRECTORY` to rebuild
the analysis modules and hash their artifacts, including on a warm build.
It writes `frozen-seal.json`, `frozen-analysis.json`, and `frozen-analysis.txt` under
`IE_PROJECTION_OUTPUT_DIR`, or a fresh temporary directory when unset.
-/

open Lean Lean.Elab.Command LeanInformationAudit
open LeanInformationAudit.Tests.Projection
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAuditAnalysis.FrozenRootAnalysis

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

run_cmd do
  let root := frozenInformationRootId
  let env ← getEnv
  if (SealRecords.analysisForRoot? env root).isSome ||
      env.contains (root.str "__system_catalog_irredundant") then
    throwError "InformationRoot closure contains analysis staging"
  let rootId := mkIdent (`_root_ ++ root)
  let counts := SealRecords.forRoot (← getEnv) root
  unless counts.size == 11 do throwError "frozen root arena inventory"
  let observed := counts.flatMap (·.theorems.map (·.uniqueCaptureCount))
  unless observed.qsort (· < ·) == (#[570, 12, 20, 56, 240, 968, 6, 12, 48, 60, 2]).qsort
      (· < ·) do throwError "frozen root reseal counts: {observed}"
  let sealArtifact ← liftTermElabM <| serializeSealArtifact counts
  unless Sha256.hex sealArtifact.toUTF8 ==
      "994ff97c3d0e4f031b6ca34e0a14349788dcded230256b5df14da0bbfc6dc168" do
    throwError "frozen root seal digest"
  elabCommand (← `(command| #stage_information_analysis root $rootId:ident))
  let some analysis := SealRecords.analysisForRoot? (← getEnv) root
    | throwError "missing frozen root analysis state"
  unless analysis.records.size == 11 do throwError "frozen root analysis inventory"
  for name in analysis.declarationNames do
    elabCommand (← `(command| #print axioms $(mkIdent name)))
  let sealPath := Syntax.mkStrLit (← fixturePath "frozen-seal.json")
  let analysisPath := Syntax.mkStrLit (← fixturePath "frozen-analysis.json")
  let asciiPath := Syntax.mkStrLit (← fixturePath "frozen-analysis.txt")
  elabCommand (← `(command| #export_information_analysis root $rootId:ident
    output $sealPath:str analysis_output $analysisPath:str ascii_output $asciiPath:str))
  let json ← liftIO <| IO.FS.readFile (← fixturePath "frozen-analysis.json")
  let .ok artifact := Json.parse json | throwError "frozen root JSON"
  unless (artifact.getObjValAs? (Array Json) "catalogs").toOption.map (·.size) == some 11 do
    throwError "frozen root analysis arena inventory"
  logInfo m!"frozen root analysis: 11 arenas; unique counts {observed}"

end LeanInformationAuditAnalysis.FrozenRootAnalysis
