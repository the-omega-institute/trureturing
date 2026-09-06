import D5.S3.ConceptDynamics.InformationEscape.InformationRoot
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Projection.FixtureState

open Lean Lean.Elab.Command LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Projection.FrozenRootV3

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

run_cmd do
  let root := frozenInformationRootId
  let counts := SealRecords.forRoot (← getEnv) root
  unless counts.size == 11 do throwError "frozen root arena inventory"
  let observed := counts.flatMap (·.theorems.map (·.uniqueCaptureCount))
  unless observed.qsort (· < ·) == (#[570, 12, 20, 56, 240, 968, 6, 12, 48, 60, 2]).qsort
      (· < ·) do throwError "frozen root reseal counts: {observed}"
  let v2 := serializeV2Artifact counts
  unless Sha256.hex v2.toUTF8 ==
      "6da462e5cbfa01261eb820dd4c236f647632fd36fe8df9a391ec5ed9800cd16b" do
    throwError "frozen root v2 digest"
  let some analysis := SealRecords.analysisForRoot? (← getEnv) root
    | throwError "missing frozen root analysis state"
  unless analysis.records.size == 11 do throwError "frozen root analysis inventory"
  for name in analysis.declarationNames do
    elabCommand (← `(command| #print axioms $(mkIdent name)))
  let v2Path := Syntax.mkStrLit (← fixturePath "frozen-v2.json")
  let v3Path := Syntax.mkStrLit (← fixturePath "frozen-v3.json")
  let asciiPath := Syntax.mkStrLit (← fixturePath "frozen-v3.txt")
  let rootId := mkIdent (`_root_ ++ root)
  elabCommand (← `(command| #export_information_analysis root $rootId:ident
    output $v2Path:str analysis_output $v3Path:str ascii_output $asciiPath:str))
  let json ← liftIO <| IO.FS.readFile (← fixturePath "frozen-v3.json")
  let .ok artifact := Json.parse json | throwError "frozen root JSON"
  unless (artifact.getObjValAs? (Array Json) "catalogs").toOption.map (·.size) == some 11 do
    throwError "frozen root v3 arena inventory"
  logInfo m!"frozen root v3: 11 arenas; unique counts {observed}"

end LeanInformationAudit.Tests.Projection.FrozenRootV3
