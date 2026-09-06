import LeanInformationAudit.Projection.KernelProjection
import LeanInformationAudit.Projection.AsciiHierarchy
import LeanInformationAudit.Tests.Projection.FixtureState

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.CIRPT

namespace LeanInformationAudit.Tests.Projection.Bounded

abbrev arena : Arena := Arena.ofFintype (Bool × Bool × Bool)

def unit (readout : Bool × Bool × Bool → Bool) : TheoremUnit arena where
  primitives := {
    Index := Fin 1
    indexFintype := inferInstance
    indexDecidableEq := inferInstance
    atom := fun _ => ⟨.cut, cutKernel readout⟩ }
  Statement := True
  proof := trivial

def aFirst := unit (fun p => p.1)
def bSecond := unit (fun p => p.2.1)
def cThird := unit (fun p => p.2.2)

abbrev catalog : Catalog arena := Catalog.ofVector ![aFirst, bSecond, cThird]

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

theorem cube_relations_distinct : ∀ left right : Finset (Fin 3),
    catalog.generatedKernel left = catalog.generatedKernel right ↔ left = right := by decide

run_cmd do
  let prepare := do
    (prepareKernelProjection (← mkConstWithFreshMVarLevels ``catalog)
      (← mkConstWithFreshMVarLevels ``arena) #[``aFirst, ``bSecond, ``cThird]
      `Bounded `cube ``arena `BoundedProjection).run #[]
  let ((projection, _, layers), declarations) ← liftTermElabM prepare
  let ((repeated, _, repeatedLayers), _) ← liftTermElabM prepare
  unless !projection.completeLatticeMaterialized do throwError "bounded projection flag"
  unless projection.nodes.size == 6 do throwError "bounded cube must omit two singleton interiors"
  let keys := projection.nodes.map (·.key)
  unless keys == #["K_", "K_0", "K_0_1", "K_0_2", "K_1_2", "K_0_1_2"] do
    throwError "bounded cube node inventory: {keys}"
  unless projection.nodes.map (·.escapeCount) == #[56, 24, 8, 8, 8, 0] do
    throwError "bounded cube escape counts"
  unless projection.leaveOneOut.size == 3 &&
      projection.leaveOneOut.all (fun row => keys.contains row.node && row.uniqueCaptureCount == 8) do
    throwError "bounded cube leave-one-out boundary"
  unless projection.edges.size == 6 && projection.edges.all (·.isCover) do
    throwError "bounded cube cover transitions"
  unless projection.edges.all (fun row => keys.contains row.source && keys.contains row.target) do
    throwError "bounded cube edge references"
  unless projection.certifiedChains.size == 1 do throwError "bounded cube schedule inventory"
  let schedule := projection.certifiedChains[0]!
  unless schedule.nodes == #["K_", "K_0", "K_0_1", "K_0_1_2"] &&
      schedule.increments == #[32, 16, 8] && schedule.stepClasses == #["strict", "strict", "strict"] do
    throwError "bounded cube strict schedule"
  for i in [:schedule.generators.size] do
    unless projection.edges.any (fun row => row.source == schedule.nodes[i]! &&
        row.target == schedule.nodes[i + 1]! && row.theoremName == schedule.generators[i]!) do
      throwError "bounded cube missing certified schedule edge"
  unless layers.map (·.layers.map (·.count)) == #[#[0, 32, 16, 8]] do
    throwError "bounded cube layered capture"
  unless projection.multiplicitySpectrum.map (·.count) == #[0, 24, 24, 8] do
    throwError "bounded cube multiplicity spectrum"
  unless projection.toJson.compress == repeated.toJson.compress && layers == repeatedLayers do
    throwError "bounded cube JSON determinism"
  let .ok ascii := renderAsciiHierarchy `Bounded `cube ``arena projection
    | throwError "bounded cube ASCII projection"
  let .ok repeatedAscii := renderAsciiHierarchy `Bounded `cube ``arena repeated
    | throwError "bounded cube repeated ASCII projection"
  unless ascii == repeatedAscii do throwError "bounded cube ASCII determinism"
  for declaration in declarations do
    liftCoreM <| addDecl declaration
    for name in declaration.getNames do
      elabCommand (← `(command| #print axioms $(mkIdent name)))
  modifyEnv (projectionFixtureStore.addEntry · projection)

/-- error: IE-C041 IncompleteKernelProjectionBoundary root=Bounded catalog=cube missing=["K_0_1_2"] -/
#guard_msgs in
run_cmd do
  let projection := (projectionFixtureStore.getState (← getEnv))[0]!
  let mutated := { projection with nodes := projection.nodes.filter (·.key != "K_0_1_2") }
  match mutated.validateReferences `Bounded `cube with
  | .error message => throwError message
  | .ok () => pure ()

#print axioms arena
#print axioms unit
#print axioms aFirst
#print axioms bSecond
#print axioms cThird
#print axioms catalog
#print axioms cube_relations_distinct

end LeanInformationAudit.Tests.Projection.Bounded
