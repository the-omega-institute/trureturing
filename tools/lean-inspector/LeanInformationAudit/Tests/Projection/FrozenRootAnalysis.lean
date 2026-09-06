import D5.S3.ConceptDynamics.InformationEscape.InformationRoot
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Projection.FixtureState

open Lean Lean.Elab.Command LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Projection.FrozenRootAnalysis

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
  let sealArtifact := serializeSealArtifact counts
  unless Sha256.hex sealArtifact.toUTF8 ==
      "5e4660aeaab2f81cb6ba78e20ad5d8423dde2994cd682c8e0d93066435819e37" do
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

end LeanInformationAudit.Tests.Projection.FrozenRootAnalysis
