import LeanInformationAudit.Tests.Projection.AnalysisSeal

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/--
info: node-count rejected IE-C042 KernelProjectionCertificateMismatch root=LeanInformationAudit.Tests.Projection.AnalysisSeal catalog=importedBool component=node:K_:escape_count expected=2 actual=3
edge-omission rejected IE-C040 InvalidGeneratorTransition root=LeanInformationAudit.Tests.Projection.AnalysisSeal catalog=importedBool from=K_ to=K_0 theorem=LeanInformationAudit.Tests.ImportClosureProducer.importedTheorem.«LeanInformationAudit.Tests.Projection.AnalysisSeal/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__information_unit reason=missing-certified-transition
edge-certificate rejected IE-C042 KernelProjectionCertificateMismatch root=LeanInformationAudit.Tests.Projection.AnalysisSeal catalog=importedBool component=edge:K_:K_0:LeanInformationAudit.Tests.ImportClosureProducer.importedTheorem.«LeanInformationAudit.Tests.Projection.AnalysisSeal/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__information_unit:certificate expected="EmissionMutations.K__add_0" actual="Nat.zero_lt_one"
cover-flag rejected IE-C040 InvalidGeneratorTransition root=LeanInformationAudit.Tests.Projection.AnalysisSeal catalog=importedBool from=K_ to=K_0 theorem=LeanInformationAudit.Tests.ImportClosureProducer.importedTheorem.«LeanInformationAudit.Tests.Projection.AnalysisSeal/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__information_unit reason=cover-classification-mismatch
layer-inclusion rejected IE-C031 InvalidLayerChain root=LeanInformationAudit.Tests.Projection.AnalysisSeal catalog=importedBool chain=canonical layer=0 reason=certified-snapshot-mismatch
refinement-proof rejected IE-C027 UncertifiedKernelRefinement root=LeanInformationAudit.Tests.Projection.AnalysisSeal catalog=importedBool finer=LeanInformationAudit.Tests.ImportClosureProducer.importedTheorem.«LeanInformationAudit.Tests.Projection.AnalysisSeal/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__information_unit coarser=LeanInformationAudit.Tests.ImportClosureProducer.importedTheorem.«LeanInformationAudit.Tests.Projection.AnalysisSeal/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__information_unit missing=proof
-/
#guard_msgs in
run_cmd do
  let root := `LeanInformationAudit.Tests.Projection.AnalysisSeal
  let some counts := (SealRecords.forRoot (← getEnv) root)[0]?
    | throwError "missing sealed fixture"
  let ((projection, analysis, layers), declarations) ← liftTermElabM do
    (prepareKernelProjection (← mkConstWithFreshMVarLevels counts.catalog.catalogName)
      (← mkConstWithFreshMVarLevels counts.catalog.arenaName)
      (counts.catalog.units.map (·.unitName)) root counts.catalog.catalogId
      counts.catalog.arenaName `EmissionMutations).run #[]
  for declaration in declarations do liftCoreM <| addDecl declaration
  let record : AnalysisCatalogRecord := { counts, projection, analysis, layerChains := layers }
  let system := root.str "__system_catalog_irredundant"
  let _ ← liftTermElabM <| serializeAnalysisArtifact root #[record] system
  let candidates : Array (String × AnalysisCatalogRecord) := #[
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
      let _ ← liftTermElabM <| serializeAnalysisArtifact root #[candidate] system
      pure "ACCEPTED"
    catch error =>
      let message ← error.toMessageData.toString
      pure ("rejected " ++ message)
    messages := messages.push (label ++ " " ++ result)
  logInfo (String.intercalate "\n" messages.toList)
