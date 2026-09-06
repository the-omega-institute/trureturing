import LeanInformationAudit.ProofBuilder
import LeanInformationAudit.KernelProjection
import LeanInformationAudit.V3Inventory
import LeanInformationAudit.V3Bindings

namespace LeanInformationAudit

open Lean Lean.Meta
open D5.S3.ConceptDynamics.InformationEscape

/-- The complete CIRPT-41 catalog inventory, assembled only after proof construction. -/
structure V3CatalogRecord where
  counts : SealArenaRecord
  projection : KernelProjectionRecord
  analysis : AnalysisProjectionRecord
  layerChains : Array LayerChainRow

private def sortedNames (names : Array Name) : Array Name :=
  names.toList.eraseDups.toArray.qsort fun a b => a.toString < b.toString

private def roleTotalsJson (rows : Array (String × Nat)) : Json :=
  Json.mkObj <| (rows.qsort fun a b => a.1 < b.1).toList.map fun (key, value) =>
    (key, toJson value)

private def occurrenceJson (record : SealArenaRecord) (occurrence : SealTheoremRecord) : Json :=
  Json.mkObj [
    ("theorem", toJson occurrence.theoremName.toString),
    ("catalog_membership", Json.mkObj [
      ("root_id", toJson record.catalog.rootId.toString),
      ("catalog_id", toJson record.catalog.catalogId.toString)]),
    ("unit", toJson occurrence.unitName.toString),
    ("primitive_count", toJson occurrence.primitiveCount),
    ("primitive_axes", toJson occurrence.primitiveAxes),
    ("primitive_kernel_address", toJson occurrence.primitiveKernelAddress),
    ("full_escape_count", toJson occurrence.fullEscapeCount),
    ("without_escape_count", toJson occurrence.withoutEscapeCount),
    ("unique_capture_count", toJson occurrence.uniqueCaptureCount),
    ("unique_capture_by_role_signature", roleTotalsJson occurrence.roleSignatureHistogram),
    ("gain_rate", exactRateJson occurrence.uniqueCaptureCount record.offDiagonalPairCount),
    ("lowers_escape", toJson (decide (0 < occurrence.uniqueCaptureCount))),
    ("certificate", toJson occurrence.certificateName.toString)]

private def overlapJson (denominator : Nat) (rows : Array OverlapRow) : Json :=
  let sorted := rows.qsort fun a b => a.left.toString < b.left.toString ||
    (a.left == b.left && a.right.toString < b.right.toString)
  Json.arr (sorted.map (OverlapRow.toJson denominator))

private def refinementJson (rows : Array RefinementRow) : Json :=
  let sorted := rows.qsort fun a b => a.finer.toString < b.finer.toString ||
    (a.finer == b.finer && a.coarser.toString < b.coarser.toString)
  Json.arr (sorted.map RefinementRow.toJson)

private def equivalenceJson (rows : Array EquivalenceRow) : Json :=
  let canonical := rows.map fun row => { row with members := sortedNames row.members }
  let sorted := canonical.qsort fun a b =>
    (a.members[0]?.getD Name.anonymous).toString <
      (b.members[0]?.getD Name.anonymous).toString
  Json.arr (sorted.map EquivalenceRow.toJson)

/-- V3 catalog serialization has its own exact inventory; the v2 writer is untouched. -/
def v3CatalogJson (record : V3CatalogRecord) : Json :=
  let counts := record.counts
  let denominator := counts.offDiagonalPairCount
  let theorems := counts.theorems.qsort fun a b => a.theoremName.toString < b.theoremName.toString
  let spectrum := record.analysis.spectrum.qsort fun a b => a.k < b.k
  let layers := record.layerChains.qsort fun a b => a.chainId < b.chainId
  let kind := counts.catalog.catalogKind.artifactName
  Json.mkObj [
    ("catalog_id", toJson counts.catalog.catalogId.toString),
    ("catalog_kind", toJson kind),
    ("object_arena", toJson counts.catalog.arenaName.toString),
    ("proof_method", toJson counts.proofMethod),
    ("state_card", toJson counts.stateCard),
    ("off_diagonal_pair_count", toJson denominator),
    ("full_escape_count", toJson counts.fullEscapeCount),
    ("full_escape_rate", exactRateJson counts.fullEscapeCount denominator),
    ("catalog_verdict", toJson record.projection.verdict),
    ("redundant_theorems", namesJson (sortedNames record.projection.redundantIndices)),
    ("verdict_certificate", toJson counts.irredundantCertificateName.toString),
    ("exclusive_capture_total", toJson record.analysis.exclusiveCaptureTotal),
    ("pairwise_capture_overlap", overlapJson denominator record.analysis.overlap),
    ("kernel_refinement", refinementJson record.analysis.refinement),
    ("kernel_equivalence_classes", equivalenceJson record.analysis.equivalenceClasses),
    ("catalog_unique_capture_by_role_signature", roleTotalsJson record.analysis.roleTotals),
    ("capture_multiplicity_spectrum", Json.arr <| spectrum.map (SpectrumRow.toJson denominator)),
    ("layer_chains", Json.arr <| layers.map (LayerChainRow.toJson denominator)),
    ("kernel_projection", record.projection.toJson),
    ("theorems", Json.arr <| theorems.map (occurrenceJson counts))]

private def coincidenceClassesJson (records : Array V3CatalogRecord) : Json := Id.run do
  let occurrences := records.flatMap fun record => record.counts.theorems
  let addresses := occurrences.map (·.primitiveKernelAddress)
    |>.toList.eraseDups.toArray.qsort (· < ·)
  let mut classes := #[]
  for address in addresses do
    let members := occurrences.filter (·.primitiveKernelAddress == address)
      |>.map (·.unitName) |> sortedNames
    if members.size > 1 then
      classes := classes.push <| Json.mkObj [
        ("primitive_kernel_address", toJson address),
        ("occurrences", namesJson members),
        ("serializer", toJson "primitive-kernel-ordinal-partition-v1"),
        ("diagnostic_only", toJson true)]
  return Json.arr classes

private def mismatch (root catalog : Name) (component : String) (expected actual : Json) :
    MetaM Unit :=
  throwError "IE-C028 AnalysisCertificateMismatch root={root} catalog={catalog} \
component={component} expected={expected.compress} actual={actual.compress}"

private def requireName (root catalog : Name) (component : String) (name : Name)
    (certificate : Bool := false) : MetaM Unit := do
  let info := (← getEnv).find? name
  let valid := match info with
    | some (.thmInfo _) => true
    | some _ => !certificate
    | none => false
  unless valid do
    mismatch root catalog component (toJson (if certificate then "Lean-theorem" else
      "Lean-declaration")) (toJson name.toString)

private def validateInventory (root : Name) (record : V3CatalogRecord) : MetaM Unit := do
  let counts := record.counts
  let catalog := counts.catalog.catalogId
  let size := counts.theorems.size
  let nodes := record.projection.nodes.size
  let env ← getEnv
  for occurrence in counts.theorems do
    unless occurrence.registrationModuleName == env.header.mainModule ||
        env.allImportedModuleNames.contains occurrence.registrationModuleName do
      mismatch root catalog "registration_modules" (toJson "import-closure-module")
        (toJson occurrence.registrationModuleName.toString)
  match record.projection.validateReferences root catalog with
  | .ok () => pure ()
  | .error message => throwError message
  let dimensions := #[("occurrences", 1, min 1 size),
    ("kernel_projection.nodes", 1, min 1 nodes),
    ("pairwise_capture_overlap", size * (size + 1) / 2, record.analysis.overlap.size),
    ("kernel_refinement", size * size, record.analysis.refinement.size),
    ("capture_multiplicity_spectrum", size + 1, record.analysis.spectrum.size),
    ("layer_chains", 1, min 1 record.layerChains.size),
    ("kernel_projection.leave_one_out", size, record.projection.leaveOneOut.size),
    ("kernel_projection.refinement_matrix", nodes * nodes,
      record.projection.refinementMatrix.size),
    ("kernel_projection.overlap_matrix", nodes * (nodes + 1) / 2,
      record.projection.overlapMatrix.size),
    ("kernel_projection.multiplicity_spectrum", size + 1,
      record.projection.multiplicitySpectrum.size),
    ("kernel_projection.certified_chains", record.layerChains.size,
      record.projection.certifiedChains.size)]
  for (component, expected, actual) in dimensions do
    unless expected == actual do mismatch root catalog component (toJson expected) (toJson actual)
  unless counts.catalog.rootId == root do
    mismatch root catalog "root_id" (toJson root.toString) (toJson counts.catalog.rootId.toString)
  let spectrumIndices := record.analysis.spectrum.map (·.k) |>.qsort (· < ·)
  unless spectrumIndices == Array.range (size + 1) do
    mismatch root catalog "spectrum-indices" (toJson (Array.range (size + 1)))
      (toJson spectrumIndices)
  unless record.projection.multiplicitySpectrum == record.analysis.spectrum do
    mismatch root catalog "kernel_projection.multiplicity_spectrum"
      (toJson (record.analysis.spectrum.map (·.count)))
      (toJson (record.projection.multiplicitySpectrum.map (·.count)))
  let total := counts.theorems.foldl (fun total row => total + row.uniqueCaptureCount) 0
  unless total == record.analysis.exclusiveCaptureTotal do
    mismatch root catalog "exclusive_capture_total" (toJson total)
      (toJson record.analysis.exclusiveCaptureTotal)
  let spectrumTotal := record.analysis.spectrum.foldl (fun total row => total + row.count) 0
  unless spectrumTotal == counts.offDiagonalPairCount do
    mismatch root catalog "capture_multiplicity_spectrum.total" (toJson counts.offDiagonalPairCount)
      (toJson spectrumTotal)
  let zero := record.analysis.spectrum.find? (·.k == 0) |>.map (·.count) |>.getD 0
  let unique := record.analysis.spectrum.find? (·.k == 1) |>.map (·.count) |>.getD 0
  unless zero == counts.fullEscapeCount && unique == total do
    mismatch root catalog "capture_multiplicity_spectrum.boundary"
      (toJson #[counts.fullEscapeCount, total]) (toJson #[zero, unique])
  let roleRows := counts.theorems.flatMap (·.roleSignatureHistogram)
  let roleKeys := roleRows.map (·.1) |>.toList.eraseDups.toArray.qsort (· < ·)
  let expectedRoles := roleKeys.map fun key =>
    (key, (roleRows.filter (·.1 == key)).foldl (fun total row => total + row.2) 0)
  unless roleTotalsJson expectedRoles == roleTotalsJson record.analysis.roleTotals do
    mismatch root catalog "catalog_unique_capture_by_role_signature"
      (roleTotalsJson expectedRoles) (roleTotalsJson record.analysis.roleTotals)
  let memberNames := sortedNames (counts.theorems.map (·.unitName))
  let pairOrder (left right : Name × Name) := left.1.toString < right.1.toString ||
    (left.1 == right.1 && left.2.toString < right.2.toString)
  let directed := memberNames.flatMap fun finer => memberNames.map (finer, ·)
  let upper := directed.filter fun (left, right) => left.toString ≤ right.toString
  let actualDirected := record.analysis.refinement.map (fun row => (row.finer, row.coarser))
    |>.qsort pairOrder
  let actualUpper := record.analysis.overlap.map (fun row => (row.left, row.right))
    |>.qsort pairOrder
  unless actualDirected == directed.qsort pairOrder do
    mismatch root catalog "kernel_refinement.members" (toJson "complete-directed-member-pairs")
      (toJson "invalid-member-pairs")
  unless actualUpper == upper.qsort pairOrder do
    mismatch root catalog "pairwise_capture_overlap.members" (toJson "canonical-upper-triangle")
      (toJson "invalid-member-pairs")
  for row in record.analysis.refinement do
    unless #["equal", "strictly_finer", "strictly_coarser", "incomparable"].contains
        row.comparison do
      mismatch root catalog "kernel_refinement.comparison" (toJson "KernelComparison")
        (toJson row.comparison)
    let included := row.comparison == "equal" || row.comparison == "strictly_finer"
    unless row.proofName.isSome == included && row.counterexample.isSome == !included do
      throwError "IE-C027 UncertifiedKernelRefinement root={root} catalog={catalog} \
finer={row.finer} coarser={row.coarser} missing={if included then "proof" else "counterexample"}"
  let equivalenceMembers := record.analysis.equivalenceClasses.flatMap (·.members)
  unless sortedNames equivalenceMembers == memberNames && equivalenceMembers.size == size do
    mismatch root catalog "kernel_equivalence_classes" (namesJson memberNames)
      (namesJson equivalenceMembers)
  let p := record.projection
  let a := record.analysis
  let references : Array (String × Name) :=
    #[("object_arena", counts.catalog.arenaName), ("catalog", counts.catalog.catalogName)] ++
    counts.theorems.flatMap (fun row => #[("theorem", row.theoremName), ("unit", row.unitName),
      ("realization", row.realizationName)]) ++
    p.nodes.flatMap (fun row => row.generators.map ("kernel_projection.generators", ·)) ++
    p.edges.map (fun row => ("kernel_projection.theorem", row.theoremName)) ++
    p.collapsedAdditions.map (fun row => ("kernel_projection.theorem", row.theoremName)) ++
    p.leaveOneOut.map (fun row => ("kernel_projection.theorem", row.theoremName)) ++
    p.certifiedChains.flatMap (fun row => row.generators.map ("kernel_projection.generators", ·)) ++
    (a.refinement ++ p.refinementMatrix).flatMap (fun row =>
      #[("refinement.finer", row.finer), ("refinement.coarser", row.coarser)]) ++
    (a.overlap ++ p.overlapMatrix).flatMap (fun row =>
      #[("overlap.left", row.left), ("overlap.right", row.right)]) ++
    a.equivalenceClasses.flatMap (fun row => row.members.map ("equivalence.members", ·)) ++
    record.layerChains.flatMap (fun row => row.kernels.map ("layer_chains.kernel", ·)) ++
    p.redundantIndices.map ("redundant_indices", ·)
  for (component, name) in references do requireName root catalog component name
  let certificates := #[counts.irredundantCertificateName] ++
    counts.theorems.map (·.certificateName) ++ p.nodes.map (·.relationCertificate) ++
    p.edges.map (·.certificate) ++ p.collapsedAdditions.map (·.equalityCertificate) ++
    p.leaveOneOut.map (·.certificate) ++
    p.certifiedChains.flatMap (fun row => row.stepCertificates.push row.partitionCertificate) ++
    (a.refinement ++ p.refinementMatrix).filterMap (·.proofName) ++
    (a.overlap ++ p.overlapMatrix).map (·.certificate) ++
    a.equivalenceClasses.map (·.certificate) ++
    (a.spectrum ++ p.multiplicitySpectrum).map (·.certificate) ++
    record.layerChains.flatMap (fun row => row.inclusionCertificates ++
      row.layers.map (·.certificate) ++ #[row.unresolved.certificate, row.partitionCertificate]) ++
    (a.certificates ++ p.certificates).map (·.2)
  for name in certificates do requireName root catalog "certificate" name true

/-- Check the staged theorem against the actual root and complete `catalogAt` family.
The certificate remains in Lean: CIRPT-41 permits no extra root certificate field. -/
def serializeV3Artifact (rootId : Name) (records : Array V3CatalogRecord)
    (systemCertificate : Name) : MetaM String := do
  let env ← getEnv
  let some (.thmInfo certificate) := env.find? systemCertificate
    | throwError "IE-C028 AnalysisCertificateMismatch root={rootId} catalog=system \
component=system-certificate expected=Lean-theorem actual={systemCertificate}"
  let positive := certificate.type.isAppOf ``SystemCatalogIrredundant
  let proposition := if positive then certificate.type else
    if certificate.type.isAppOf ``Not then certificate.type.appArg! else certificate.type
  unless proposition.isAppOf ``SystemCatalogIrredundant do
    mismatch rootId `system "system-certificate-type" (toJson "SystemCatalogIrredundant")
      (toJson systemCertificate.toString)
  if records.isEmpty then
    mismatch rootId `system "catalogs" (toJson "nonempty") (toJson (0 : Nat))
  let suite := proposition.appArg!
  unless ← isDefEq (← mkAppM ``DesignatedRootCatalogSuite.rootId #[suite]) (toExpr rootId) do
    mismatch rootId `system "system-root" (toJson rootId.toString) (toJson systemCertificate.toString)
  let indexType ← mkAppM ``DesignatedRootCatalogSuite.CatalogIndex #[suite]
  unless ← isDefEq indexType (mkApp (mkConst ``Fin) (mkNatLit records.size)) do
    mismatch rootId `system "system-catalog-domain" (toJson records.size)
      (toJson systemCertificate.toString)
  let mut occurrenceKeys : Array (Name × Name) := #[]
  for record in records do
    for row in record.counts.theorems do
      let key := (record.counts.catalog.arenaName, row.theoremName)
      if occurrenceKeys.contains key then
        mismatch rootId record.counts.catalog.catalogId "occurrence-key"
          (toJson "unique") (toJson s!"{key.1}/{key.2}")
      occurrenceKeys := occurrenceKeys.push key
  for (record, i) in records.zipIdx do
    let packed ← mkAppM ``DesignatedRootCatalogSuite.catalogAt
      #[suite, ← ProjectionProof.fin i records.size]
    let actual ← mkAppM ``PackedCatalog.catalog #[packed]
    unless ← isDefEq actual (← mkConstWithFreshMVarLevels record.counts.catalog.catalogName) do
      mismatch rootId `system "system-catalog-membership"
        (toJson record.counts.catalog.catalogName.toString) (toJson systemCertificate.toString)
    validateInventory rootId record
    let reflected ← validateCertifiedProjection rootId record.counts.catalog.catalogId actual
      record.projection record.analysis record.layerChains
    if record.counts.catalog.catalogKind == .canonicalMaximal &&
        record.projection.verdict == "redundant" then
      let zeroIndices := record.counts.theorems.filter (·.uniqueCaptureCount == 0) |>.map (·.index)
      throwError "IE-C033 IncompleteRedundantIndexSet key={rootId}/{record.counts.catalog.catalogId} \
expected=[] certified={(toJson (zeroIndices.qsort (· < ·))).compress} phase=canonical-export"
    validateV3Bindings rootId actual reflected (← mkAppM ``PackedCatalog.arena #[packed])
      record.counts record.projection
  let records := records.qsort fun a b =>
    a.counts.catalog.arenaName.toString < b.counts.catalog.arenaName.toString ||
      (a.counts.catalog.arenaName == b.counts.catalog.arenaName &&
        a.counts.catalog.catalogId.toString < b.counts.catalog.catalogId.toString)
  let modules := sortedNames <| records.flatMap fun record =>
    record.counts.theorems.map (·.registrationModuleName)
  let artifact := Json.mkObj [
    ("schema", toJson "lean-intrinsic-information-escape-v3"),
    ("root_id", toJson rootId.toString),
    ("seal_scope", toJson "import-closure"),
    ("registration_modules", namesJson modules),
    ("system_catalog_irredundant", toJson positive),
    ("kernel_address_coincidence_classes", coincidenceClassesJson records),
    ("catalogs", Json.arr <| records.map v3CatalogJson)]
  match validateV3Inventory rootId artifact with
  | .error message => throwError message
  | .ok () => pure ()
  return artifact.pretty

end LeanInformationAudit
