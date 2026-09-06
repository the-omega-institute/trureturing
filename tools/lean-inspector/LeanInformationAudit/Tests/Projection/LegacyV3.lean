import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Projection.FixtureState

open Lean Lean.Elab.Command LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Projection.LegacyV3

def objectArena : Arena := Arena.ofFintype Bool
def lawArena : PrimitiveLawArena where
  toArena := objectArena
  signature := {
    Index := Fin 1
    indexFintype := inferInstance
    indexDecidableEq := inferInstance
    Output := fun _ => Bool
    outputDecidableEq := fun _ => inferInstance
    axis := fun _ => .cut
    readoutAxisNotAnchor := by simp
    AnchorIndex := Fin 0
    anchorFintype := inferInstance
    anchorDecidableEq := inferInstance }
  Law := fun _ => True
local instance : DecidableEq lawArena.State := lawArena.toArena.stateDecidableEq
def fixtureRealization : PrimitiveRealization lawArena.signature where
  readout := fun _ state => state
  anchor := Fin.elim0
information_theorem localTheorem in lawArena primitives fixtureRealization
  : lawArena.Law fixtureRealization := by trivial
run_cmd do
  let moduleName := Syntax.mkStrLit (← getEnv).header.mainModule.toString
  elabCommand (← `(command| expect_information_occurrence localTheorem
    in lawArena from $moduleName:str))

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

run_cmd do
  let path ← fixturePath "legacy-v3.json"
  elabCommand (← `(command| #seal_information_theory analysis_output $(Syntax.mkStrLit path):str))

/-- info: legacy v3 identities are qualified; v2 identities retained -/
#guard_msgs in
run_cmd do
  let root := (← getEnv).header.mainModule
  let some counts := (SealRecords.forRoot (← getEnv) root)[0]?
    | throwError "missing legacy seal"
  let .ok json := Json.parse (← liftIO <| IO.FS.readFile (← fixturePath "legacy-v3.json"))
    | throwError "legacy JSON"
  let catalogJson := (json.getObjValAs? (Array Json) "catalogs").toOption.get![0]!
  let row := (catalogJson.getObjValAs? (Array Json) "theorems").toOption.get![0]!
  for (key, suffix) in #[("unit", theoremUnitSuffix), ("certificate", "__lowers_escape")] do
    let expected := catalogQualifiedName root counts.catalog.arenaName counts.catalog.catalogId
      ``localTheorem suffix
    unless (row.getObjValAs? String key).toOption == some expected.toString do
      throwError "v3 occurrence identity is unqualified: {key}"
  unless counts.theorems[0]?.map (·.unitName) == some (``localTheorem |>.str theoremUnitSuffix) do
    throwError "v2 occurrence identity changed"
  logInfo "legacy v3 identities are qualified; v2 identities retained"

end LeanInformationAudit.Tests.Projection.LegacyV3
