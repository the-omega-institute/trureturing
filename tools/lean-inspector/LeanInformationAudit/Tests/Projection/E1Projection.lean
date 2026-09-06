import LeanInformationAudit.KernelProjection
import LeanInformationAudit.AsciiHierarchy
import LeanInformationAudit.Tests.Projection.KernelLaws
import LeanInformationAudit.Tests.Projection.FixtureState

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit

namespace LeanInformationAudit.Tests.Projection

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

run_cmd do
  let ((projection, _, layers), declarations) ← liftTermElabM do
    (prepareKernelProjection (← mkConstWithFreshMVarLevels ``catalog)
      (← mkConstWithFreshMVarLevels ``arena) #[``aFst, ``bSnd, ``cId]
      `E1 `catalog ``arena `E1Projection {
        complete := true
        schedules := #[ ("fst-snd-id", #[0, 1, 2]), ("id-fst-snd", #[2, 0, 1]) ]
      }).run #[]
  unless projection.nodes.size == 4 do throwError "E1 quotient size"
  unless projection.nodes.map (·.escapeCount) == #[12, 4, 4, 0] do
    throwError "E1 escape counts: {projection.nodes.map (·.escapeCount)}"
  unless projection.edges.size == 7 do throwError "E1 strict edges"
  unless (projection.edges.filter (·.isCover)).size == 6 do throwError "E1 labeled covers"
  let covers := (projection.edges.filter (·.isCover)).map fun edge => (edge.source, edge.target)
  unless covers.toList.eraseDups.length == 4 do throwError "E1 cover endpoint pairs"
  unless projection.certifiedChains.map (·.increments) == #[#[8, 4, 0], #[12, 0, 0]] do
    throwError "E1 schedule increments"
  unless layers.map (·.layers.map (·.count)) == #[#[0, 8, 4, 0], #[0, 12, 0, 0]] do
    throwError "E1 layered captures"
  unless projection.leaveOneOut.all (·.uniqueCaptureCount == 0) do throwError "E1 leave one out"
  for declaration in declarations do
    liftCoreM <| addDecl declaration
    for name in declaration.getNames do
      elabCommand (← `(command| #print axioms $(mkIdent name)))
  modifyEnv (projectionFixtureStore.addEntry · projection)
  let .ok ascii := renderAsciiHierarchy `E1 `catalog ``arena projection
    | throwError "E1 renderer"
  liftIO <| IO.FS.writeFile (← fixturePath "e1.json") projection.toJson.pretty
  liftIO <| IO.FS.writeFile (← fixturePath "e1.txt") ascii

end LeanInformationAudit.Tests.Projection
