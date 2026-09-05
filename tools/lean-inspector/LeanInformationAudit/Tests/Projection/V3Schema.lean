import LeanInformationAudit.V3Artifact

open Lean LeanInformationAudit

namespace LeanInformationAudit.Tests.Projection.V3Schema

private def theoremRecord : SealTheoremRecord := {
  theoremName := ``True.intro
  unitName := ``True.intro
  realizationName := ``True.intro
  certificateName := ``True.intro
  registrationModuleName := `Init
  index := 0
  primitiveCount := 1
  primitiveAxes := #["cut"]
  primitiveKernelAddress := "sha256:fixture"
  uniqueCaptureCount := 2
  fullEscapeCount := 0
  withoutEscapeCount := 2
  roleSignatureHistogram := #[("1000", 2)]
  proofMethod := "direct" }

private def catalogRecord : V3CatalogRecord := {
  counts := {
    catalog := {
      rootId := `Root
      catalogId := `Catalog
      catalogKind := .canonicalMaximal
      arenaName := `Arena
      catalogName := `Catalog
      units := #[]
      compatibilityV2 := false }
    irredundantCertificateName := ``True.intro
    proofMethod := "direct"
    stateCard := 2
    offDiagonalPairCount := 2
    fullEscapeCount := 0
    theorems := #[theoremRecord] }
  projection := { denominator := 2 }
  analysis := {}
  layerChains := #[] }

private def checkKeys (value : Json) (expected : Array String) : CoreM Unit := do
  let actual := value.getObj?.toOption.get!.toArray.map (·.1) |>.qsort (· < ·)
  unless actual == expected.qsort (· < ·) do
    throwError "v3 exhaustive key-set mismatch: {actual}"

run_cmd do
  let catalog := v3CatalogJson catalogRecord
  Lean.Elab.Command.liftCoreM <| checkKeys catalog #["catalog_id", "catalog_kind", "object_arena",
    "proof_method", "state_card", "off_diagonal_pair_count", "full_escape_count",
    "full_escape_rate", "catalog_verdict", "redundant_theorems", "verdict_certificate",
    "exclusive_capture_total", "pairwise_capture_overlap", "kernel_refinement",
    "kernel_equivalence_classes", "catalog_unique_capture_by_role_signature",
    "capture_multiplicity_spectrum", "layer_chains", "kernel_projection", "theorems"]
  let occurrence := (catalog.getObjValAs? (Array Json) "theorems").toOption.get![0]!
  Lean.Elab.Command.liftCoreM <| checkKeys occurrence #["theorem", "catalog_membership", "unit",
    "primitive_count", "primitive_axes", "primitive_kernel_address", "full_escape_count",
    "without_escape_count", "unique_capture_count", "unique_capture_by_role_signature",
    "gain_rate", "lowers_escape", "certificate"]
  unless catalog.compress == (v3CatalogJson catalogRecord).compress do
    throwError "v3 catalog serialization is nondeterministic"

run_cmd do
  let check (value : Json) (keys : Array String) :=
    Lean.Elab.Command.liftCoreM <| checkKeys value keys
  check (exactRateJson 1 2) #["numerator", "denominator"]
  check (OverlapRow.toJson 2 {
    left := `left, right := `right, count := 1, certificate := ``Nat.zero_lt_one })
    #["left", "right", "count", "rate", "certificate"]
  check (RefinementRow.toJson {
    finer := `finer, coarser := `coarser, comparison := "equal",
    proofName := some ``Nat.zero_lt_one, counterexample := none })
    #["finer", "coarser", "comparison", "proof", "counterexample"]
  check (EquivalenceRow.toJson { members := #[`member], certificate := ``Nat.zero_lt_one })
    #["members", "certificate"]
  check (SpectrumRow.toJson 2 { k := 1, count := 2, certificate := ``Nat.zero_lt_one })
    #["k", "count", "rate", "certificate"]
  check (ProjectionNode.toJson 2 {
    key := "node", generators := #[`member], escapeCount := 0,
    relationCertificate := ``Nat.zero_lt_one })
    #["node_key", "selected_cardinality", "generators", "escape_count", "escape_rate",
      "relation_certificate"]
  check (ProjectionEdge.toJson 2 {
    source := "from", target := "to", theoremName := `member, isCover := true,
    captureCount := 2, certificate := ``Nat.zero_lt_one })
    #["from", "to", "theorem", "is_cover", "capture_count", "capture_rate", "certificate"]
  check (CollapsedAddition.toJson {
    atNode := "node", theoremName := `member, equalityCertificate := ``Nat.zero_lt_one })
    #["at", "theorem", "equality_certificate"]
  check (LeaveOneOutRow.toJson 2 {
    theoremName := `member, node := "node", uniqueCaptureCount := 2,
    certificate := ``Nat.zero_lt_one })
    #["theorem", "node", "unique_capture_count", "unique_capture_rate", "certificate"]
  check (CertifiedScheduleRow.toJson {
    chainId := "chain", nodes := #["from", "to"], generators := #[`member],
    stepClasses := #["strict"], increments := #[2], stepCertificates := #[``Nat.zero_lt_one],
    terminalEscapeCount := 0, partitionCertificate := ``Nat.zero_lt_one })
    #["chain_id", "nodes", "generators", "step_classes", "increments", "step_certificates",
      "terminal_escape_count", "partition_certificate"]
  let layer := LayerChainRow.toJson 2 {
    chainId := "chain", kernels := #[`kernel], inclusionCertificates := #[],
    layers := #[{ count := 0, certificate := ``Nat.zero_lt_one }],
    unresolved := { count := 2, certificate := ``Nat.zero_lt_one },
    partitionCertificate := ``Nat.zero_lt_one }
  check layer #["chain_id", "kernels", "inclusion_certificates", "layers", "unresolved",
    "partition_certificate"]
  check ((layer.getObjValAs? (Array Json) "kernels").toOption.get![0]!) #["position", "kernel"]
  check ((layer.getObjValAs? (Array Json) "layers").toOption.get![0]!)
    #["position", "count", "rate", "certificate"]
  check ((layer.getObjVal? "unresolved").toOption.get!) #["count", "rate", "certificate"]

/-- error: IE-C028 AnalysisCertificateMismatch root=Root catalog=Catalog component=fixture-key-set expected=["count"] actual=["count","extra"] -/
#guard_msgs in
run_cmd do
  match validateV3KeySet `Root `Catalog "fixture" #["count"]
      (Json.mkObj [("count", toJson (1 : Nat)), ("extra", Json.null)]) with
  | .ok () => pure ()
  | .error message => throwError message

/-- error: IE-C028 AnalysisCertificateMismatch root=Root catalog=system component=system-certificate-type expected="SystemCatalogIrredundant" actual="Nat.zero_lt_one" -/
#guard_msgs in
run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    serializeV3Artifact `Root #[catalogRecord] ``Nat.zero_lt_one

end LeanInformationAudit.Tests.Projection.V3Schema
