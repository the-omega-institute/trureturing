import LeanInformationAudit.KernelProjection
import LeanInformationAudit.ProjectionValidation
import LeanInformationAudit.V3Artifact
import LeanInformationAudit.AsciiHierarchy

namespace LeanInformationAudit

open Lean Lean.Meta Lean.Elab.Command
open D5.S3.ConceptDynamics.InformationEscape

structure PreparedAnalysis where
  declarations : Array Declaration
  records : Array V3CatalogRecord
  systemCertificate : Name

/-- Build analysis certificates from the same prepared catalogs as the v2 seal. -/
def prepareAnalysisProofs (catalogs : Array PreparedCatalog) (proofs : PreparedProofs) :
    CommandElabM PreparedAnalysis := do
  let root := (← getEnv).header.mainModule
  let ((records, systemCertificate), declarations) ← liftTermElabM do
    (do
      let mut records := #[]
      let mut packed := #[]
      for prepared in catalogs, counts in proofs.records do
        let record := prepared.record
        let certPrefix := catalogQualifiedName root record.arenaName record.catalogId
          record.arenaName "__kernel_projection"
        let (projection, analysis, layerChains) ← prepareKernelProjection
          prepared.value prepared.arenaValue (record.units.map (·.unitName)) root
          record.catalogId record.arenaName certPrefix
        records := records.push { counts, projection, analysis, layerChains : V3CatalogRecord }
        packed := packed.push (← mkAppM ``PackedCatalog.mk #[prepared.arenaValue, prepared.value])
      let vector ← ProjectionProof.vector packed
      let rootExpr := toExpr root
      let suite ← mkAppM ``projectionSuite #[rootExpr, vector]
      let _ ← ProjectionProof.value (root.str "__catalog_suite") suite
      let proposition ← mkAppM ``SystemCatalogIrredundant #[suite]
      let instanceValue ← mkAppM ``projectionSystemDecidable #[rootExpr, vector]
      let certificate ← ProjectionProof.proof (root.str "__system_catalog_irredundant")
        (← mkAppOptM ``of_decide_eq_true
          #[some proposition, some instanceValue, some (← mkEqRefl (mkConst ``Bool.true))])
      pure (records, certificate) : ProjectionM _).run #[]
  pure { declarations, records, systemCertificate }

def serializeAsciiArtifact (records : Array V3CatalogRecord) : Except String String := do
  let records := records.qsort fun a b =>
    a.counts.catalog.arenaName.toString < b.counts.catalog.arenaName.toString
  let texts ← records.mapM fun record => renderAsciiHierarchy record.counts.catalog.rootId
    record.counts.catalog.catalogId record.counts.catalog.arenaName record.projection
  pure (String.intercalate "\n" texts.toList)

end LeanInformationAudit
