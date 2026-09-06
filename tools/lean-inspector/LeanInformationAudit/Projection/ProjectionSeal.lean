import LeanInformationAudit.Projection.KernelProjection
import LeanInformationAudit.Projection.ProjectionValidation
import LeanInformationAudit.Projection.V3Artifact
import LeanInformationAudit.Projection.AsciiHierarchy

namespace LeanInformationAudit

open Lean Lean.Meta Lean.Elab.Command
open D5.S3.ConceptDynamics.InformationEscape

structure PreparedAnalysis where
  declarations : Array Declaration
  records : Array V3CatalogRecord
  systemCertificate : Name

/-- Internal ceiling needed to stage the designated root's causal projection during seal. -/
def sealAnalysisMaxHeartbeats : Nat := 8000000000

private def withSealAnalysisBudget (action : Lean.Elab.Term.TermElabM α) :
    Lean.Elab.Term.TermElabM α :=
  withTheReader Core.Context
    (fun context => { context with
      maxHeartbeats := max context.maxHeartbeats sealAnalysisMaxHeartbeats }) action

/-- V3 has separate qualified companions. Frozen v2 records are never renamed. -/
def prepareV3QualifiedCounts (counts : SealArenaRecord) (available : Array Declaration) :
    ProjectionM SealArenaRecord := do
  let metadata := counts.catalog
  let options ← getOptions
  let mut certificateEnv ← getEnv
  for declaration in available do
    if declaration.getNames.all certificateEnv.contains then continue
    match certificateEnv.addDeclCore (Core.getMaxHeartbeats options).toUSize
        (maxRecDepth.get options).toUSize declaration none true with
    | .ok next => certificateEnv := next
    | .error error => throwError "{error.toMessageData options}"
  withEnv certificateEnv do
    let original ← if certificateEnv.contains metadata.catalogName then
        mkConstWithFreshMVarLevels metadata.catalogName
      else mkAppM ``Catalog.ofVector #[← ProjectionProof.vector
        (← counts.theorems.mapM fun row => mkConstWithFreshMVarLevels row.unitName)]
    let originalType ← whnf (← inferType original)
    validateCatalogArena metadata.rootId metadata.catalogId metadata.arenaName original
      originalType.appArg! counts.stateCard
  let qualified (name : Name) (suffix : String) :=
    catalogQualifiedName metadata.rootId metadata.arenaName metadata.catalogId name suffix
  let certificateAlias (source target : Name) := withEnv certificateEnv do
    if source == target then return
    let value ← mkConstWithFreshMVarLevels source
    let _ ← ProjectionProof.proof target value
  let mut theorems := #[]
  for row in counts.theorems do
    let unitName := qualified row.theoremName theoremUnitSuffix
    let realizationName := qualified row.theoremName primitiveRealizationSuffix
    let certificateName := qualified row.theoremName "__lowers_escape"
    for (source, target) in #[(row.unitName, unitName), (row.realizationName, realizationName)] do
      if source != target then
        let _ ← ProjectionProof.value target (← mkConstWithFreshMVarLevels source)
    certificateAlias row.certificateName certificateName
    theorems := theorems.push { row with unitName, realizationName, certificateName }
  let irredundantCertificateName := qualified metadata.arenaName "__catalog_irredundant"
  certificateAlias counts.irredundantCertificateName irredundantCertificateName
  let units := theorems.map fun row => {
    theoremName := row.theoremName, unitName := row.unitName, realizationName := row.realizationName,
    registrationModuleName := row.registrationModuleName, index := row.index : CatalogUnitRecord }
  return { counts with
    theorems, irredundantCertificateName,
    catalog := { metadata with units, compatibilityV2 := false } }

/-- Build analysis certificates from the same prepared catalogs as the v2 seal. -/
def prepareAnalysisProofs (catalogs : Array PreparedCatalog) (proofs : PreparedProofs) :
    CommandElabM PreparedAnalysis := do
  let root := (← getEnv).header.mainModule
  let mut records := #[]
  let mut packed := #[]
  let mut declarations := #[]
  for prepared in catalogs, counts in proofs.records do
    let ((record, packedCatalog), nextDeclarations) ← liftTermElabM do
      withSealAnalysisBudget <| (do
        let counts ← prepareV3QualifiedCounts counts proofs.declarations
        let record := prepared.record
        let certPrefix := catalogQualifiedName root record.arenaName record.catalogId
          record.arenaName "__kernel_projection"
        let (projection, analysis, layerChains) ← prepareKernelProjection
          prepared.value prepared.arenaValue (counts.theorems.map (·.unitName)) root
          record.catalogId record.arenaName certPrefix
        let packedCatalog ← mkAppM ``PackedCatalog.mk #[prepared.arenaValue, prepared.value]
        pure ({ counts, projection, analysis, layerChains : V3CatalogRecord }, packedCatalog) :
          ProjectionM _).run declarations
    records := records.push record
    packed := packed.push packedCatalog
    declarations := nextDeclarations
  let (systemCertificate, finalDeclarations) ← liftTermElabM do
    withSealAnalysisBudget <| (do
      let vector ← ProjectionProof.vector packed
      let rootExpr := toExpr root
      let suite ← mkAppM ``projectionSuite #[rootExpr, vector]
      let _ ← ProjectionProof.value (root.str "__catalog_suite") suite
      let proposition ← mkAppM ``SystemCatalogIrredundant #[suite]
      let instanceValue ← mkAppM ``projectionSystemDecidable #[rootExpr, vector]
      let certificate ← ProjectionProof.proof (root.str "__system_catalog_irredundant")
        (← mkAppOptM ``of_decide_eq_true
          #[some proposition, some instanceValue, some (← mkEqRefl (mkConst ``Bool.true))])
      pure certificate : ProjectionM _).run declarations
  pure { declarations := finalDeclarations, records, systemCertificate }

def serializeAsciiArtifact (records : Array V3CatalogRecord) : Except String String := do
  let records := records.qsort fun a b =>
    a.counts.catalog.arenaName.toString < b.counts.catalog.arenaName.toString
  let texts ← records.mapM fun record => renderAsciiHierarchy record.counts.catalog.rootId
    record.counts.catalog.catalogId record.counts.catalog.arenaName record.projection
  pure (String.intercalate "\n" texts.toList)

end LeanInformationAudit
