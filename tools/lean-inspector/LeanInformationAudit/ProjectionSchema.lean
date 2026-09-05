import Lean

namespace LeanInformationAudit

open Lean

def exactRateJson (numerator denominator : Nat) : Json :=
  Json.mkObj [("numerator", Lean.toJson numerator), ("denominator", Lean.toJson denominator)]

def namesJson (names : Array Name) : Json := Json.arr (names.map (Lean.toJson ·.toString))

structure ProjectionNode where
  key : String
  generators : Array Name
  escapeCount : Nat
  relationCertificate : Name
  deriving Inhabited, BEq, Repr

structure ProjectionEdge where
  source : String
  target : String
  theoremName : Name
  isCover : Bool
  captureCount : Nat
  certificate : Name
  deriving Inhabited, BEq, Repr

structure CollapsedAddition where
  atNode : String
  theoremName : Name
  equalityCertificate : Name
  deriving Inhabited, BEq, Repr

structure LeaveOneOutRow where
  theoremName : Name
  node : String
  uniqueCaptureCount : Nat
  certificate : Name
  deriving Inhabited, BEq, Repr

structure CertifiedScheduleRow where
  chainId : String
  nodes : Array String
  generators : Array Name
  stepClasses : Array String
  increments : Array Nat
  stepCertificates : Array Name
  terminalEscapeCount : Nat
  partitionCertificate : Name
  deriving Inhabited, BEq, Repr

structure OverlapRow where
  left : Name
  right : Name
  count : Nat
  certificate : Name
  deriving Inhabited, BEq, Repr

structure RefinementRow where
  finer : Name
  coarser : Name
  comparison : String
  proofName : Option Name
  counterexample : Option (Nat × Nat)
  deriving Inhabited, BEq, Repr

structure EquivalenceRow where
  members : Array Name
  certificate : Name
  deriving Inhabited, BEq, Repr

structure SpectrumRow where
  k : Nat
  count : Nat
  certificate : Name
  deriving Inhabited, BEq, Repr

structure LayerRow where
  count : Nat
  certificate : Name
  deriving Inhabited, BEq, Repr

structure LayerChainRow where
  chainId : String
  kernels : Array Name
  inclusionCertificates : Array Name
  layers : Array LayerRow
  unresolved : LayerRow
  partitionCertificate : Name
  deriving Inhabited, BEq, Repr

structure KernelProjectionRecord where
  completeLatticeMaterialized : Bool := false
  nodes : Array ProjectionNode := #[]
  edges : Array ProjectionEdge := #[]
  collapsedAdditions : Array CollapsedAddition := #[]
  leaveOneOut : Array LeaveOneOutRow := #[]
  certifiedChains : Array CertifiedScheduleRow := #[]
  refinementMatrix : Array RefinementRow := #[]
  overlapMatrix : Array OverlapRow := #[]
  multiplicitySpectrum : Array SpectrumRow := #[]
  redundantIndices : Array Name := #[]
  verdict : String := "irredundant"
  certificates : Array (String × Name) := #[]
  denominator : Nat := 0
  deriving Inhabited, BEq, Repr

def ProjectionNode.toJson (denominator : Nat) (node : ProjectionNode) : Json :=
  Json.mkObj [
    ("node_key", Lean.toJson node.key),
    ("selected_cardinality", Lean.toJson node.generators.size),
    ("generators", namesJson node.generators),
    ("escape_count", Lean.toJson node.escapeCount),
    ("escape_rate", exactRateJson node.escapeCount denominator),
    ("relation_certificate", Lean.toJson node.relationCertificate.toString)]

def ProjectionEdge.toJson (denominator : Nat) (edge : ProjectionEdge) : Json :=
  Json.mkObj [
    ("from", Lean.toJson edge.source), ("to", Lean.toJson edge.target),
    ("theorem", Lean.toJson edge.theoremName.toString), ("is_cover", Lean.toJson edge.isCover),
    ("capture_count", Lean.toJson edge.captureCount),
    ("capture_rate", exactRateJson edge.captureCount denominator),
    ("certificate", Lean.toJson edge.certificate.toString)]

def CollapsedAddition.toJson (row : CollapsedAddition) : Json :=
  Json.mkObj [("at", Lean.toJson row.atNode), ("theorem", Lean.toJson row.theoremName.toString),
    ("equality_certificate", Lean.toJson row.equalityCertificate.toString)]

def LeaveOneOutRow.toJson (denominator : Nat) (row : LeaveOneOutRow) : Json :=
  Json.mkObj [("theorem", Lean.toJson row.theoremName.toString), ("node", Lean.toJson row.node),
    ("unique_capture_count", Lean.toJson row.uniqueCaptureCount),
    ("unique_capture_rate", exactRateJson row.uniqueCaptureCount denominator),
    ("certificate", Lean.toJson row.certificate.toString)]

def CertifiedScheduleRow.toJson (row : CertifiedScheduleRow) : Json :=
  Json.mkObj [("chain_id", Lean.toJson row.chainId), ("nodes", Lean.toJson row.nodes),
    ("generators", namesJson row.generators), ("step_classes", Lean.toJson row.stepClasses),
    ("increments", Lean.toJson row.increments), ("step_certificates", namesJson row.stepCertificates),
    ("terminal_escape_count", Lean.toJson row.terminalEscapeCount),
    ("partition_certificate", Lean.toJson row.partitionCertificate.toString)]

def OverlapRow.toJson (denominator : Nat) (row : OverlapRow) : Json :=
  Json.mkObj [("left", Lean.toJson row.left.toString), ("right", Lean.toJson row.right.toString),
    ("count", Lean.toJson row.count), ("rate", exactRateJson row.count denominator),
    ("certificate", Lean.toJson row.certificate.toString)]

def RefinementRow.toJson (row : RefinementRow) : Json :=
  Json.mkObj [("finer", Lean.toJson row.finer.toString), ("coarser", Lean.toJson row.coarser.toString),
    ("comparison", Lean.toJson row.comparison),
    ("proof", row.proofName.map (Lean.toJson ·.toString) |>.getD Json.null),
    ("counterexample", row.counterexample.map (fun pair => Lean.toJson #[pair.1, pair.2])
      |>.getD Json.null)]

def EquivalenceRow.toJson (row : EquivalenceRow) : Json :=
  Json.mkObj [("members", namesJson row.members),
    ("certificate", Lean.toJson row.certificate.toString)]

def SpectrumRow.toJson (denominator : Nat) (row : SpectrumRow) : Json :=
  Json.mkObj [("k", Lean.toJson row.k), ("count", Lean.toJson row.count),
    ("rate", exactRateJson row.count denominator),
    ("certificate", Lean.toJson row.certificate.toString)]

def LayerChainRow.toJson (denominator : Nat) (row : LayerChainRow) : Json :=
  let countRow (layer : LayerRow) := [
    ("count", Lean.toJson layer.count), ("rate", exactRateJson layer.count denominator),
    ("certificate", Lean.toJson layer.certificate.toString)]
  Json.mkObj [("chain_id", Lean.toJson row.chainId),
    ("kernels", Json.arr <| row.kernels.mapIdx fun i name =>
      Json.mkObj [("position", Lean.toJson i), ("kernel", Lean.toJson name.toString)]),
    ("inclusion_certificates", namesJson row.inclusionCertificates),
    ("layers", Json.arr <| row.layers.mapIdx fun i layer =>
      Json.mkObj (("position", Lean.toJson i) :: countRow layer)),
    ("unresolved", Json.mkObj (countRow row.unresolved)),
    ("partition_certificate", Lean.toJson row.partitionCertificate.toString)]

def KernelProjectionRecord.canonical (projection : KernelProjectionRecord) :
    KernelProjectionRecord :=
  { projection with
    nodes := projection.nodes.qsort fun a b =>
      a.generators.size < b.generators.size ||
        (a.generators.size == b.generators.size && a.key < b.key)
    edges := projection.edges.qsort fun a b =>
      a.source < b.source || (a.source == b.source &&
        (a.target < b.target || (a.target == b.target &&
          a.theoremName.toString < b.theoremName.toString)))
    collapsedAdditions := projection.collapsedAdditions.qsort fun a b =>
      a.atNode < b.atNode ||
        (a.atNode == b.atNode && a.theoremName.toString < b.theoremName.toString)
    leaveOneOut := projection.leaveOneOut.qsort fun a b =>
      a.theoremName.toString < b.theoremName.toString
    certifiedChains := projection.certifiedChains.qsort fun a b => a.chainId < b.chainId
    refinementMatrix := projection.refinementMatrix.qsort fun a b =>
      a.finer.toString < b.finer.toString ||
        (a.finer == b.finer && a.coarser.toString < b.coarser.toString)
    overlapMatrix := projection.overlapMatrix.qsort fun a b =>
      a.left.toString < b.left.toString ||
        (a.left == b.left && a.right.toString < b.right.toString)
    multiplicitySpectrum := projection.multiplicitySpectrum.qsort fun a b => a.k < b.k
    redundantIndices := projection.redundantIndices.qsort fun a b => a.toString < b.toString
    certificates := projection.certificates.qsort fun a b =>
      a.1 < b.1 || (a.1 == b.1 && a.2.toString < b.2.toString) }

def KernelProjectionRecord.toJson (projection : KernelProjectionRecord) : Json :=
  let p := projection.canonical
  Json.mkObj [("projection_kind", Lean.toJson "boundary-and-certified-chains"),
    ("complete_lattice_materialized", Lean.toJson p.completeLatticeMaterialized),
    ("nodes", Json.arr (p.nodes.map (ProjectionNode.toJson p.denominator))),
    ("edges", Json.arr (p.edges.map (ProjectionEdge.toJson p.denominator))),
    ("collapsed_additions", Json.arr (p.collapsedAdditions.map CollapsedAddition.toJson)),
    ("leave_one_out", Json.arr (p.leaveOneOut.map (LeaveOneOutRow.toJson p.denominator))),
    ("certified_chains", Json.arr (p.certifiedChains.map CertifiedScheduleRow.toJson)),
    ("refinement_matrix", Json.arr (p.refinementMatrix.map RefinementRow.toJson)),
    ("overlap_matrix", Json.arr (p.overlapMatrix.map (OverlapRow.toJson p.denominator))),
    ("multiplicity_spectrum", Json.arr (p.multiplicitySpectrum.map
      (SpectrumRow.toJson p.denominator))),
    ("redundant_indices", namesJson p.redundantIndices), ("verdict", Lean.toJson p.verdict),
    ("certificates", Json.mkObj (p.certificates.toList.map fun (key, name) =>
      (key, Lean.toJson name.toString)))]

def KernelProjectionRecord.validateReferences (root catalog : Name)
    (projection : KernelProjectionRecord) : Except String Unit := do
  let keys := projection.nodes.map (·.key)
  let references := projection.edges.flatMap (fun row => #[row.source, row.target]) ++
    projection.collapsedAdditions.map (·.atNode) ++ projection.leaveOneOut.map (·.node) ++
    projection.certifiedChains.flatMap (·.nodes)
  let missing := references.filter (fun key => !keys.contains key)
    |>.toList.eraseDups.toArray.qsort (· < ·)
  unless missing.isEmpty do
    throw s!"IE-C041 IncompleteKernelProjectionBoundary root={root} catalog={catalog} \
missing={(Lean.toJson missing).compress}"
  for key in keys do
    unless (keys.filter (· == key)).size == 1 do
      throw s!"IE-C039 InvalidGeneratedKernelNode root={root} catalog={catalog} \
node={key} reason=duplicate-node-key"

/-- Admission clients have no accessor for presentation data. -/
def rejectProjectionAdmission (consumer : Name) (field : String) (root catalog : Name) :
    Except String Unit :=
  .error s!"IE-C043 KernelProjectionUsedForAdmission consumer={consumer} field={field} \
root={root} catalog={catalog}"

end LeanInformationAudit
