import LeanInformationAudit.Projection.KernelProjection
import LeanInformationAudit.Projection.ProjectionValidation
import LeanInformationAudit.Projection.AnalysisArtifact
import LeanInformationAudit.Projection.AsciiHierarchy

namespace LeanInformationAudit

open Lean Lean.Meta Lean.Elab.Command
open D5.S3.ConceptDynamics.InformationEscape

structure PreparedAnalysis where
  declarations : Array Declaration
  records : Array AnalysisCatalogRecord
  systemCertificate : Name

/-- Internal ceiling for staging the designated root's causal analysis. -/
def analysisMaxHeartbeats : Nat := 8000000000

private def withAnalysisBudget (action : Lean.Elab.Term.TermElabM α) :
    Lean.Elab.Term.TermElabM α :=
  withTheReader Core.Context
    (fun context => { context with
      maxHeartbeats := max context.maxHeartbeats analysisMaxHeartbeats }) action

/-- Analysis uses qualified companions while seal records keep their original names. -/
def prepareAnalysisQualifiedCounts (counts : SealArenaRecord) (available : Array Declaration) :
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
    let certificateName := qualified row.theoremName row.certificate.suffix
    for (source, target) in #[(row.unitName, unitName), (row.realizationName, realizationName)] do
      if source != target then
        let _ ← ProjectionProof.value target (← mkConstWithFreshMVarLevels source)
    certificateAlias row.certificateName certificateName
    let certificate := match row.certificate with
      | .positive _ => OccurrenceCertificate.positive certificateName
      | .trivial _ => .trivial certificateName
    theorems := theorems.push { row with unitName, realizationName, certificate }
  let verdictName := qualified metadata.arenaName counts.verdict.suffix
  certificateAlias counts.verdict.name verdictName
  let verdict := match counts.verdict with
    | .irredundant _ => CatalogVerdict.irredundant verdictName
    | .redundant _ => .redundant verdictName
  let units := theorems.map fun row => {
    theoremName := row.theoremName, unitName := row.unitName, realizationName := row.realizationName,
    registrationModuleName := row.registrationModuleName, index := row.index : CatalogUnitRecord }
  return { counts with
    theorems, verdict,
    catalog := { metadata with units, localSealNames := false } }

/-- Build analysis certificates from catalogs already published by seal. -/
def prepareAnalysisProofs (root : Name) (sealedRecords : Array SealArenaRecord) :
    CommandElabM PreparedAnalysis := do
  let mut records := #[]
  let mut packed := #[]
  let mut declarations := #[]
  for counts in sealedRecords do
    let ((record, packedCatalog), nextDeclarations) ← liftTermElabM do
      withAnalysisBudget <| (do
        let counts ← prepareAnalysisQualifiedCounts counts #[]
        let record := counts.catalog
        let catalog ← mkConstWithFreshMVarLevels record.catalogName
        let arena := (← whnf (← inferType catalog)).appArg!
        let certPrefix := catalogQualifiedName root record.arenaName record.catalogId
          record.arenaName "__kernel_projection"
        let (projection, analysis, layerChains) ← prepareKernelProjection
          catalog arena (counts.theorems.map (·.unitName)) root
          record.catalogId record.arenaName certPrefix
        let packedCatalog ← mkAppM ``PackedCatalog.mk #[arena, catalog]
        pure ({ counts, projection, analysis, layerChains : AnalysisCatalogRecord },
          packedCatalog) :
          ProjectionM _).run declarations
    records := records.push record
    packed := packed.push packedCatalog
    declarations := nextDeclarations
  let (systemCertificate, finalDeclarations) ← liftTermElabM do
    withAnalysisBudget <| (do
      let vector ← ProjectionProof.vector packed
      let rootExpr := toExpr root
      let suite ← mkAppM ``projectionSuite #[rootExpr, vector]
      let _ ← ProjectionProof.value (root.str "__catalog_suite") suite
      let proposition ← mkAppM ``SystemCatalogIrredundant #[suite]
      let negative := sealedRecords.findIdx? fun record => match record.verdict with
        | .irredundant _ => false | .redundant _ => true
      let certificate ← if let some i := negative then do
          let some record := sealedRecords[i]? | throwError "missing redundant catalog"
          let notIrredundant ← mkAppM ``Iff.mp #[
            ← mkAppM ``Catalog.catalogRedundant_iff_not_catalogIrredundant
              #[← mkConstWithFreshMVarLevels record.catalog.catalogName],
            ← mkConstWithFreshMVarLevels record.verdict.name]
          let proof ← withLocalDeclD `positive proposition fun h => do
            mkLambdaFVars #[h] (mkApp notIrredundant
              (mkApp h (← ProjectionProof.fin i sealedRecords.size)))
          let proof ← mkAppOptM ``id #[some (← mkAppM ``Not #[proposition]), some proof]
          ProjectionProof.proof (root.str "__system_catalog_not_irredundant") proof
        else do
          let instanceValue ← mkAppM ``projectionSystemDecidable #[rootExpr, vector]
          ProjectionProof.proof (root.str "__system_catalog_irredundant")
            (← mkAppOptM ``of_decide_eq_true
              #[some proposition, some instanceValue, some (← mkEqRefl (mkConst ``Bool.true))])
      pure certificate : ProjectionM _).run declarations
  pure { declarations := finalDeclarations, records, systemCertificate }

def serializeAsciiArtifact (records : Array AnalysisCatalogRecord) : Except String String := do
  let records := records.qsort fun a b =>
    a.counts.catalog.arenaName.toString < b.counts.catalog.arenaName.toString
  let texts ← records.mapM fun record => renderAsciiHierarchy record.counts.catalog.rootId
    record.counts.catalog.catalogId record.counts.catalog.arenaName record.projection
  pure (String.intercalate "\n" texts.toList)

end LeanInformationAudit
