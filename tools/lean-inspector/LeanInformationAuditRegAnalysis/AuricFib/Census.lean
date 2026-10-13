import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import LeanInformationAuditRegAnalysis.Projection.ProjectionRefinement
import LeanInformationAuditRegAnalysis.AuricFib.Source
import LeanInformationAuditRegAnalysis.Projection.ProjectionSchema

namespace LeanInformationAudit.AuricFib
open Lean
open D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window)
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.CIRPT

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq

/-- Degenerate finite and unbounded domains have no ordered-pair rate. -/
def pairRate (cardinality : Option Nat) (count : Nat) : Option Json := do
  let n ← cardinality
  if n < 2 then none else some (exactRateJson count (n * (n-1)))

def pairsJson (pairs : Finset (Window × Window)) : Json :=
  Json.arr <| (modes.flatMap fun a => modes.filterMap fun b =>
    if (a, b) ∈ pairs then some (toJson [modeIndex a, modeIndex b]) else none).toArray

def relationJson (node : nativeCatalog.GeneratedKernel) : Json :=
  toJson (modes.toArray.map fun a => modes.toArray.map fun b => node.relationB a b)

def subsetForMask (mask : Nat) : Finset (Fin 4) :=
  ((List.finRange 4).filter (fun i => mask.testBit i.val)).toFinset

def namesOf (selected : Finset (Fin 4)) : Json :=
  toJson (((List.finRange 4).filter (· ∈ selected)).map readoutName)

def kernelJson : Json := Id.run do
  let mut representatives : Array (Finset (Fin 4)) := #[]
  let mut subsets : Array Json := #[]
  for mask in [:16] do
    let selected := subsetForMask mask
    let node := nativeCatalog.generatedKernel selected
    let index := match representatives.findIdx? (fun existing =>
        Catalog.GeneratedKernel.nodesEqB (nativeCatalog.generatedKernel existing) node) with
      | some index => index
      | none => representatives.size
    if index = representatives.size then representatives := representatives.push selected
    subsets := subsets.push <| Json.mkObj [
      ("readouts", namesOf selected), ("node", toJson index),
      ("escape_count", toJson node.escapeCount)]
  let nodes := representatives.mapIdx fun index selected =>
    let node := nativeCatalog.generatedKernel selected
    Json.mkObj [("node", toJson index), ("generators", namesOf selected),
      ("relation", relationJson node), ("escape_pairs", pairsJson node.escapeAt),
      ("escape_count", toJson node.escapeCount),
      ("escape_rate", (pairRate (some nativeArena.card) node.escapeCount).getD Json.null)]
  let mut edges : Array Json := #[]
  for i in [:representatives.size] do
    for j in [:representatives.size] do
      let coarser := nativeCatalog.generatedKernel representatives[i]!
      let finer := nativeCatalog.generatedKernel representatives[j]!
      if projectionRefinesB finer coarser && !projectionRefinesB coarser finer then
        edges := edges.push <| Json.mkObj [("from", toJson i), ("to", toJson j),
          ("is_cover", toJson (decide (projectionCover nativeCatalog representatives[i]! finer))),
          ("capture_count", toJson (coarser.edgeCaptureCount finer))]
  return Json.mkObj [
    ("readout_order", toJson ((List.finRange 4).map readoutName)),
    ("full_relation", relationJson (nativeCatalog.generatedKernel nativeCatalog.fullIndexSet)),
    ("generated_nodes", Json.arr nodes), ("subsets", Json.arr subsets),
    ("strict_edges", Json.arr edges), ("complete_lattice_materialized", toJson true),
    ("kind", toJson "exact finite extensional analysis; no proof-escape certification")]

def fused := nativeCatalog.fusedCounts enumeration (Catalog.finIndexEnumeration 4)

def uniqueJson : Json := Json.arr <| (List.finRange 4).toArray.map fun i =>
  Json.mkObj [("readout", toJson (readoutName i)),
    ("count", toJson (fused.unique i)),
    ("pairs", pairsJson (nativeCatalog.uniqueCapturePairs i)),
    ("rate", (pairRate (some nativeArena.card) (fused.unique i)).getD Json.null),
    ("leave_one_out_count", toJson (fused.without i)),
    ("leave_one_out_pairs", pairsJson (nativeCatalog.escapePairs (nativeCatalog.without i))),
    ("leave_one_out_rate", (pairRate (some nativeArena.card) (fused.without i)).getD Json.null)]

structure ScheduleInput where
  initial : Finset (Fin 4)
  layers : List (Fin 4)

def parseSchedule (request : Json) : Except String ScheduleInput := do
  let parseNames (value : Json) := do
    let names ← value.getArr?
    names.toList.mapM (fun value => value.getStr? >>= readoutIndex)
  let initial ← match (request.getObjVal? "initial_readouts").toOption with
    | none => pure [] | some value => parseNames value
  let layers ← match (request.getObjVal? "layers").toOption with
    | none => pure [1, 2, 3, 0] | some value => parseNames value
  unless layers.length ≤ 64 do throw "at most 64 finite successor layers are supported"
  unless initial.toFinset ∪ layers.toFinset = nativeCatalog.fullIndexSet do
    throw "the complete atom,seam,guard,reply bundle must remain in the final layer"
  return ⟨initial.toFinset, layers⟩

def selectedAt (schedule : ScheduleInput) (position : Nat) : Finset (Fin 4) :=
  schedule.initial ∪ (schedule.layers.take position).toFinset

/-- Cumulative selections preserve every weak refinement, including repeated readouts. -/
def layerChain (schedule : ScheduleInput) : LayerChain nativeArena where
  length := schedule.layers.length
  kernel := fun j => nativeCatalog.generatedKernelRelation (selectedAt schedule j.val)
  refines := by
    intro j x y related
    apply nativeCatalog.indistinguishable_mono _ related
    apply Finset.union_subset_union_right
    intro i hi
    exact List.mem_toFinset.mpr
      ((List.take_subset_take_left schedule.layers (Nat.le_succ j.val)) (List.mem_toFinset.mp hi))

def layersJson (schedule : ScheduleInput) : Json := Id.run do
  let chain := layerChain schedule
  let positions := List.finRange (chain.length + 1)
  let layers := positions.toArray.map fun i =>
    let count := chain.layeredCaptureCount i
    let collapsed := if i.val = 0 then false else
      Catalog.GeneratedKernel.nodesEqB
        (nativeCatalog.generatedKernel (selectedAt schedule (i.val-1)))
        (nativeCatalog.generatedKernel (selectedAt schedule i.val))
    Json.mkObj [("position", toJson i.val), ("readouts", namesOf (selectedAt schedule i.val)),
      ("count", toJson count), ("pairs", pairsJson (chain.layeredCapturePairs i)),
      ("rate", (pairRate (some nativeArena.card) count).getD Json.null),
      ("collapsed", toJson collapsed)]
  let addresses := modes.flatMap fun a => modes.filterMap fun b =>
    if a = b then none else
      let layer := positions.find? (fun i => decide ((a, b) ∈ chain.layeredCapturePairs i))
      some <| Json.mkObj [("pair", toJson [modeIndex a, modeIndex b]),
        ("first_layer", toJson (layer.map (·.val)))]
  let counts := positions.foldl (fun total i => total + chain.layeredCaptureCount i) 0
  return Json.mkObj [("layers", Json.arr layers),
    ("initial_readouts", namesOf schedule.initial),
    ("schedule", toJson (schedule.layers.map readoutName)),
    ("unresolved", Json.mkObj [("count", toJson chain.unresolvedCount),
      ("pairs", pairsJson chain.unresolvedPairs),
      ("rate", (pairRate (some nativeArena.card) chain.unresolvedCount).getD Json.null)]),
    ("first_capture", toJson addresses),
    ("partition_count", toJson (counts + chain.unresolvedCount)),
    ("ordered_pair_denominator", toJson (nativeArena.card * (nativeArena.card-1)))]

end LeanInformationAudit.AuricFib
