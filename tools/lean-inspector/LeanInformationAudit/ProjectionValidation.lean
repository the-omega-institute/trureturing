import LeanInformationAudit.ProjectionSchema

namespace LeanInformationAudit

open Lean

private def certificateMismatch (root catalog : Name) (component : String)
    (expected actual : Json) : Except String Unit := do
  unless expected == actual do
    throw s!"IE-C042 KernelProjectionCertificateMismatch root={root} catalog={catalog} \
component={component} expected={expected.compress} actual={actual.compress}"

private def invalidNode (root catalog : Name) (key reason : String) : Except String Unit :=
  .error s!"IE-C039 InvalidGeneratedKernelNode root={root} catalog={catalog} \
node={key} reason={reason}"

private def invalidTransition (root catalog : Name) (source target : String)
    (theoremName : Name) (reason : String) : Except String Unit :=
  .error s!"IE-C040 InvalidGeneratorTransition root={root} catalog={catalog} \
from={source} to={target} theorem={theoremName} reason={reason}"

private def sameTransition (left right : ProjectionEdge) : Bool :=
  left.source == right.source && left.target == right.target &&
    left.theoremName == right.theoremName

private def sameCollapsed (left right : CollapsedAddition) : Bool :=
  left.atNode == right.atNode && left.theoremName == right.theoremName

/-- Compares a candidate output snapshot to freshly kernel-certified in-memory rows.
No file or artifact is consumed, and this comparison supplies no admission evidence. -/
def validateProjectionSnapshot (root catalog : Name)
    (certified candidate : KernelProjectionRecord) : Except String Unit := do
  candidate.validateReferences root catalog
  let expected := certified.canonical
  let actual := candidate.canonical
  let missing := expected.nodes.filter (fun node =>
      !actual.nodes.any (fun other => node.key == other.key))
    |>.map (·.key) |>.qsort (· < ·)
  unless missing.isEmpty do
    throw s!"IE-C041 IncompleteKernelProjectionBoundary root={root} catalog={catalog} \
missing={(Lean.toJson missing).compress}"
  for node in actual.nodes do
    if actual.nodes.any fun other => other.key != node.key &&
        (other.relationCertificate == node.relationCertificate ||
          other.generators == node.generators) then
      let aliases := actual.nodes.filter fun other =>
        other.relationCertificate == node.relationCertificate || other.generators == node.generators
      let alias := aliases.find? fun other => !expected.nodes.any (fun row => row.key == other.key)
      invalidNode root catalog (alias.getD node).key "duplicate-extensional-node"
    let some original := expected.nodes.find? (fun row => row.key == node.key)
      | invalidNode root catalog node.key "uncertified-node"
    unless node.generators == original.generators &&
        node.relationCertificate == original.relationCertificate do
      invalidNode root catalog node.key "representative-mismatch"
    certificateMismatch root catalog s!"node:{node.key}:escape_count"
      (Lean.toJson original.escapeCount) (Lean.toJson node.escapeCount)
  for edge in actual.edges do
    let some original := expected.edges.find? (sameTransition edge)
      | invalidTransition root catalog edge.source edge.target edge.theoremName
          "uncertified-transition"
    unless (actual.edges.filter (sameTransition edge)).size == 1 do
      invalidTransition root catalog edge.source edge.target edge.theoremName
        "duplicate-transition"
    unless edge.isCover == original.isCover do
      invalidTransition root catalog edge.source edge.target edge.theoremName
        "cover-classification-mismatch"
    certificateMismatch root catalog
      s!"edge:{edge.source}:{edge.target}:{edge.theoremName}:capture_count"
      (Lean.toJson original.captureCount) (Lean.toJson edge.captureCount)
    certificateMismatch root catalog
      s!"edge:{edge.source}:{edge.target}:{edge.theoremName}:certificate"
      (Lean.toJson original.certificate.toString) (Lean.toJson edge.certificate.toString)
  for edge in expected.edges do
    unless actual.edges.any (sameTransition edge) do
      invalidTransition root catalog edge.source edge.target edge.theoremName
        "missing-certified-transition"
  for row in actual.collapsedAdditions do
    let some original := expected.collapsedAdditions.find? (sameCollapsed row)
      | invalidTransition root catalog row.atNode row.atNode row.theoremName
          "uncertified-collapsed-addition"
    unless (actual.collapsedAdditions.filter (sameCollapsed row)).size == 1 do
      invalidTransition root catalog row.atNode row.atNode row.theoremName
        "duplicate-collapsed-addition"
    certificateMismatch root catalog s!"collapsed:{row.atNode}:{row.theoremName}:certificate"
      (Lean.toJson original.equalityCertificate.toString)
      (Lean.toJson row.equalityCertificate.toString)
  for row in expected.collapsedAdditions do
    unless actual.collapsedAdditions.any (sameCollapsed row) do
      invalidTransition root catalog row.atNode row.atNode row.theoremName
        "missing-collapsed-addition"
  certificateMismatch root catalog "denominator"
    (Lean.toJson expected.denominator) (Lean.toJson actual.denominator)
  certificateMismatch root catalog "complete_lattice_materialized"
    (Lean.toJson expected.completeLatticeMaterialized)
    (Lean.toJson actual.completeLatticeMaterialized)
  certificateMismatch root catalog "leave_one_out"
    (Json.arr <| expected.leaveOneOut.map (LeaveOneOutRow.toJson expected.denominator))
    (Json.arr <| actual.leaveOneOut.map (LeaveOneOutRow.toJson actual.denominator))
  certificateMismatch root catalog "certified_chains"
    (Json.arr <| expected.certifiedChains.map CertifiedScheduleRow.toJson)
    (Json.arr <| actual.certifiedChains.map CertifiedScheduleRow.toJson)
  certificateMismatch root catalog "refinement_matrix"
    (Json.arr <| expected.refinementMatrix.map RefinementRow.toJson)
    (Json.arr <| actual.refinementMatrix.map RefinementRow.toJson)
  certificateMismatch root catalog "overlap_matrix"
    (Json.arr <| expected.overlapMatrix.map (OverlapRow.toJson expected.denominator))
    (Json.arr <| actual.overlapMatrix.map (OverlapRow.toJson actual.denominator))
  certificateMismatch root catalog "multiplicity_spectrum"
    (Json.arr <| expected.multiplicitySpectrum.map (SpectrumRow.toJson expected.denominator))
    (Json.arr <| actual.multiplicitySpectrum.map (SpectrumRow.toJson actual.denominator))
  certificateMismatch root catalog "redundant_indices"
    (namesJson expected.redundantIndices) (namesJson actual.redundantIndices)
  certificateMismatch root catalog "verdict"
    (Lean.toJson expected.verdict) (Lean.toJson actual.verdict)
  certificateMismatch root catalog "certificates"
    (Lean.toJson <| expected.certificates.map fun (key, name) => (key, name.toString))
    (Lean.toJson <| actual.certificates.map fun (key, name) => (key, name.toString))

end LeanInformationAudit
