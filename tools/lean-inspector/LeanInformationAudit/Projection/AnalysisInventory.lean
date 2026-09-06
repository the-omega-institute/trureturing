import LeanInformationAudit.Projection.ProjectionSchema

namespace LeanInformationAudit
open Lean

def validateAnalysisKeySet (root catalog : Name) (component : String) (expected : Array String)
    (value : Json) : Except String Unit := do
  let expected := expected.qsort (· < ·)
  let actual := match value.getObj? with
    | .ok object => object.toArray.map (·.1) |>.qsort (· < ·)
    | .error _ => #[]
  unless actual == expected do
    throw s!"IE-C028 AnalysisCertificateMismatch root={root} catalog={catalog} \
component={component}-key-set expected={(toJson expected).compress} actual={(toJson actual).compress}"

/-- CIRPT-41's closed containers, checked on the final JSON value before emission.
Role signatures and certificate labels are maps; their contents are bound separately. -/
def validateAnalysisInventory (root : Name) (artifact : Json) : Except String Unit := do
  let keys := validateAnalysisKeySet root `system
  let field (value : Json) (key : String) := value.getObjVal? key |>.mapError fun _ =>
    s!"IE-C028 AnalysisCertificateMismatch root={root} catalog=system \
component={key} expected=field actual=missing"
  let rows (value : Json) (key : String) := value.getObjValAs? (Array Json) key |>.mapError fun _ =>
    s!"IE-C028 AnalysisCertificateMismatch root={root} catalog=system \
component={key} expected=array actual=invalid"
  let rate (value : Json) (key : String) := do
    keys "rate" #["numerator", "denominator"] (← field value key)
  let overlap (value : Json) (key : String) := do
    for row in ← rows value key do
      keys "overlap" #["left", "right", "count", "rate", "certificate"] row
      rate row "rate"
  let refinement (value : Json) (key : String) := do
    for row in ← rows value key do
      keys "refinement" #["finer", "coarser", "comparison", "proof", "counterexample"] row
  let spectrum (value : Json) (key : String) := do
    for row in ← rows value key do
      keys "spectrum" #["k", "count", "rate", "certificate"] row
      rate row "rate"
  keys "root" #["schema", "root_id", "seal_scope", "registration_modules",
    "system_catalog_irredundant", "kernel_address_coincidence_classes", "catalogs"] artifact
  for row in ← rows artifact "kernel_address_coincidence_classes" do
    keys "coincidence-class" #["primitive_kernel_address", "occurrences", "serializer",
      "diagnostic_only"] row
  for catalog in ← rows artifact "catalogs" do
    keys "catalog" #["catalog_id", "catalog_kind", "object_arena", "proof_method", "state_card",
      "off_diagonal_pair_count", "full_escape_count", "full_escape_rate", "catalog_verdict",
      "redundant_theorems", "verdict_certificate", "exclusive_capture_total",
      "pairwise_capture_overlap", "kernel_refinement", "kernel_equivalence_classes",
      "catalog_unique_capture_by_role_signature", "capture_multiplicity_spectrum",
      "layer_chains", "kernel_projection", "theorems"] catalog
    rate catalog "full_escape_rate"
    overlap catalog "pairwise_capture_overlap"
    refinement catalog "kernel_refinement"
    spectrum catalog "capture_multiplicity_spectrum"
    for row in ← rows catalog "kernel_equivalence_classes" do
      keys "equivalence" #["members", "certificate"] row
    for row in ← rows catalog "theorems" do
      keys "occurrence" #["theorem", "catalog_membership", "unit", "primitive_count",
        "primitive_axes", "primitive_kernel_address", "full_escape_count", "without_escape_count",
        "unique_capture_count", "unique_capture_by_role_signature", "gain_rate", "lowers_escape",
        "certificate"] row
      keys "catalog_membership" #["root_id", "catalog_id"] (← field row "catalog_membership")
      rate row "gain_rate"
    for chain in ← rows catalog "layer_chains" do
      keys "layer-chain" #["chain_id", "kernels", "inclusion_certificates", "layers", "unresolved",
        "partition_certificate"] chain
      for row in ← rows chain "kernels" do
        keys "kernel-row" #["position", "kernel"] row
      for row in ← rows chain "layers" do
        keys "layer-row" #["position", "count", "rate", "certificate"] row
        rate row "rate"
      let unresolved ← field chain "unresolved"
      keys "unresolved" #["count", "rate", "certificate"] unresolved
      rate unresolved "rate"
    let projection ← field catalog "kernel_projection"
    keys "kernel-projection" #["projection_kind", "complete_lattice_materialized", "nodes", "edges",
      "collapsed_additions", "leave_one_out", "certified_chains", "refinement_matrix",
      "overlap_matrix", "multiplicity_spectrum", "redundant_indices", "verdict", "certificates"] projection
    overlap projection "overlap_matrix"
    refinement projection "refinement_matrix"
    spectrum projection "multiplicity_spectrum"
    for row in ← rows projection "nodes" do
      keys "projection-node" #["node_key", "selected_cardinality", "generators", "escape_count",
        "escape_rate", "relation_certificate"] row
      rate row "escape_rate"
    for row in ← rows projection "edges" do
      keys "projection-edge" #["from", "to", "theorem", "is_cover", "capture_count", "capture_rate",
        "certificate"] row
      rate row "capture_rate"
    for row in ← rows projection "collapsed_additions" do
      keys "collapsed-addition" #["at", "theorem", "equality_certificate"] row
    for row in ← rows projection "leave_one_out" do
      keys "leave-one-out" #["theorem", "node", "unique_capture_count", "unique_capture_rate",
        "certificate"] row
      rate row "unique_capture_rate"
    for row in ← rows projection "certified_chains" do
      keys "certified-schedule" #["chain_id", "nodes", "generators", "step_classes", "increments",
        "step_certificates", "terminal_escape_count", "partition_certificate"] row

end LeanInformationAudit
