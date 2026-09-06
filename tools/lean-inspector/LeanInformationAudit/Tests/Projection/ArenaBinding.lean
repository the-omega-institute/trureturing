import LeanInformationAudit.Tests.Projection.AnalysisSeal

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape

def SubstitutedArena : Arena := Arena.ofFintype (Fin 3)

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/--
error: IE-C028 AnalysisCertificateMismatch root=LeanInformationAudit.Tests.Projection.AnalysisSeal catalog=importedBool component=object-arena expected=certified-catalog actual=different
-/
#guard_msgs in
run_cmd do
  let root := `LeanInformationAudit.Tests.Projection.AnalysisSeal
  let some original := (SealRecords.forRoot (← getEnv) root)[0]?
    | throwError "missing sealed fixture"
  let ((record, system), declarations) ← liftTermElabM do
    (do
      let changed := { original with «catalog» := {
        original.catalog with arenaName := ``SubstitutedArena } }
      let counts ← prepareAnalysisQualifiedCounts changed #[]
      let (projection, analysis, layers) ← prepareKernelProjection
        (← mkConstWithFreshMVarLevels original.catalog.catalogName)
        (← mkConstWithFreshMVarLevels original.catalog.arenaName)
        (counts.theorems.map (·.unitName)) root counts.catalog.catalogId
        counts.catalog.arenaName `ArenaBinding
      pure ({ counts, projection, analysis, layerChains := layers : AnalysisCatalogRecord },
        root.str "__system_catalog_irredundant") : ProjectionM _).run #[]
  for declaration in declarations do liftCoreM <| addDecl declaration
  let _ ← liftTermElabM <| serializeAnalysisArtifact root #[record] system
