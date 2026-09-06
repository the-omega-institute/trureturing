import LeanInformationAudit.Tests.Projection.AnalysisSeal

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/--
info: native_decide rejected IE-C028 AnalysisCertificateMismatch root=LeanInformationAudit.Tests.Projection.AnalysisSeal catalog=importedBool component=proof-method expected=certified-catalog actual=different
invented-route rejected IE-C028 AnalysisCertificateMismatch root=LeanInformationAudit.Tests.Projection.AnalysisSeal catalog=importedBool component=proof-method expected=certified-catalog actual=different
reflected-fused-counts rejected IE-C028 AnalysisCertificateMismatch root=LeanInformationAudit.Tests.Projection.AnalysisSeal catalog=importedBool component=proof-method expected=certified-catalog actual=different
-/
#guard_msgs in
run_cmd do
  let root := `LeanInformationAudit.Tests.Projection.AnalysisSeal
  let some counts := (SealRecords.forRoot (← getEnv) root)[0]?
    | throwError "missing sealed fixture"
  let ((projection, analysis, layers), declarations) ← liftTermElabM do
    (prepareKernelProjection (← mkConstWithFreshMVarLevels counts.catalog.catalogName)
      (← mkConstWithFreshMVarLevels counts.catalog.arenaName)
      (counts.theorems.map (·.unitName)) root counts.catalog.catalogId
      counts.catalog.arenaName `RouteBinding).run #[]
  for declaration in declarations do liftCoreM <| addDecl declaration
  let record : AnalysisCatalogRecord := { counts, projection, analysis, layerChains := layers }
  let _ ← liftTermElabM <| serializeAnalysisArtifact root #[record]
    (root.str "__system_catalog_irredundant")
  let mut messages := #[]
  for route in #["native_decide", "invented-route", "reflected-fused-counts"] do
    let candidate := { record with counts := { counts with proofMethod := route } }
    let result ← try
      let _ ← liftTermElabM <| serializeAnalysisArtifact root #[candidate]
        (root.str "__system_catalog_irredundant")
      pure "ACCEPTED"
    catch error => pure ("rejected " ++ (← error.toMessageData.toString))
    messages := messages.push (route ++ " " ++ result)
  logInfo (String.intercalate "\n" messages.toList)
