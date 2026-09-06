import LeanInformationAudit.Tests.Projection.V3Seal

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/--
info: node-count rejected IE-C042
edge-omission rejected IE-C040
edge-certificate rejected IE-C042
cover-flag rejected IE-C040
layer-inclusion rejected IE-C031
refinement-proof rejected IE-C027
-/
#guard_msgs in
run_cmd do
  let root := `LeanInformationAudit.Tests.Projection.V3Seal
  let some counts := (SealRecords.forRoot (← getEnv) root)[0]?
    | throwError "missing sealed fixture"
  let ((projection, analysis, layers), declarations) ← liftTermElabM do
    (prepareKernelProjection (← mkConstWithFreshMVarLevels counts.catalog.catalogName)
      (← mkConstWithFreshMVarLevels counts.catalog.arenaName)
      (counts.catalog.units.map (·.unitName)) root counts.catalog.catalogId
      counts.catalog.arenaName `EmissionMutations).run #[]
  for declaration in declarations do liftCoreM <| addDecl declaration
  let record : V3CatalogRecord := { counts, projection, analysis, layerChains := layers }
  let system := root.str "__system_catalog_irredundant"
  let _ ← liftTermElabM <| serializeV3Artifact root #[record] system
  let candidates : Array (String × V3CatalogRecord) := #[
    ("node-count", { record with projection := { projection with
      nodes := projection.nodes.modify 0 fun node =>
        { node with escapeCount := node.escapeCount + 1 } } }),
    ("edge-omission", { record with projection := { projection with edges := #[] } }),
    ("edge-certificate", { record with projection := { projection with
      edges := projection.edges.modify 0 fun edge =>
        { edge with certificate := ``Nat.zero_lt_one } } }),
    ("cover-flag", { record with projection := { projection with
      edges := projection.edges.map fun edge => { edge with isCover := !edge.isCover } } }),
    ("layer-inclusion", { record with layerChains := layers.map fun row =>
      { row with inclusionCertificates := #[] } }),
    ("refinement-proof", { record with analysis := { analysis with
      refinement := analysis.refinement.modify 0 fun row => { row with proofName := none } } })]
  let mut messages := #[]
  for (label, candidate) in candidates do
    let result ← try
      let _ ← liftTermElabM <| serializeV3Artifact root #[candidate] system
      pure "ACCEPTED"
    catch error =>
      let message ← error.toMessageData.toString
      pure ("rejected " ++ (message.splitOn " ").head!)
    messages := messages.push (label ++ " " ++ result)
  logInfo (String.intercalate "\n" messages.toList)
