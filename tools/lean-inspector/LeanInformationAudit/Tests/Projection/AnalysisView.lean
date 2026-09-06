import LeanInformationAudit.ProjectionSeal
import LeanInformationAudit.Tests.Projection.FixtureState

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape D5.S3.ConceptDynamics.CIRPT

namespace LeanInformationAudit.Tests.Projection.AnalysisView

abbrev arena : Arena := Arena.ofFintype Bool
local instance : DecidableEq arena.State := arena.stateDecidableEq
def lawArena : PrimitiveLawArena where
  toArena := arena
  signature := {
    Index := Fin 1, indexFintype := inferInstance, indexDecidableEq := inferInstance,
    Output := fun _ => Bool, outputDecidableEq := fun _ => inferInstance,
    axis := fun _ => .cut, readoutAxisNotAnchor := by simp,
    AnchorIndex := Fin 0, anchorFintype := inferInstance, anchorDecidableEq := inferInstance }
  Law := fun _ => True
def fixtureRealization : PrimitiveRealization lawArena.signature where
  readout := fun _ state => state
  anchor := Fin.elim0
def unit : TheoremUnit arena := NativeTheoremUnit.toTheoremUnit
  (arena := lawArena) ⟨fixtureRealization, True.intro⟩
theorem first : unit.Statement := True.intro
theorem second : unit.Statement := True.intro
abbrev catalog : Catalog arena := Catalog.ofVector ![unit, unit]

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/--
info: redundant-canonical rejected IE-C033 IncompleteRedundantIndexSet key=LeanInformationAudit.Tests.Projection.AnalysisView/LeanInformationAudit.Tests.Projection.AnalysisView.catalog expected=[] certified=[0,1] phase=canonical-export
duplicate-occurrence rejected IE-C028 AnalysisCertificateMismatch root=LeanInformationAudit.Tests.Projection.AnalysisView catalog=LeanInformationAudit.Tests.Projection.AnalysisView.catalog component=occurrence-key expected="unique" actual="LeanInformationAudit.Tests.Projection.AnalysisView.arena/LeanInformationAudit.Tests.Projection.AnalysisView.first"
direct-route rejected IE-C028 AnalysisCertificateMismatch root=LeanInformationAudit.Tests.Projection.AnalysisView catalog=LeanInformationAudit.Tests.Projection.AnalysisView.catalog component=proof-method expected=certified-catalog actual=different
fused-route rejected IE-C028 AnalysisCertificateMismatch root=LeanInformationAudit.Tests.Projection.AnalysisView catalog=LeanInformationAudit.Tests.Projection.AnalysisView.catalog component=proof-method expected=certified-catalog actual=different
native-route rejected IE-C028 AnalysisCertificateMismatch root=LeanInformationAudit.Tests.Projection.AnalysisView catalog=LeanInformationAudit.Tests.Projection.AnalysisView.catalog component=proof-method expected=certified-catalog actual=different
nonempty coincidence key set passed
-/
#guard_msgs in
run_cmd do
  let root := (← getEnv).header.mainModule
  let names := #[``first, ``second]
  let qualified := names.map fun name => catalogQualifiedName root ``arena ``catalog name
    theoremUnitSuffix
  let ((record, system), declarations) ← liftTermElabM do
    (do
      let original ← mkConstWithFreshMVarLevels ``catalog
      let arena ← mkConstWithFreshMVarLevels ``arena
      for name in qualified do
        let _ ← ProjectionProof.value name (← mkConstWithFreshMVarLevels ``unit)
      let (projection, analysis, layerChains) ← prepareKernelProjection original arena qualified
        root ``catalog ``arena `AnalysisViewProjection
      let (normalized, same) ← ProjectionProof.reflectCatalog original 2
      let index ← ProjectionProof.fin 0 2
      let zero ← mkDecideProof (← mkEq
        (← mkAppM ``Catalog.uniqueCaptureCount #[normalized, index]) (mkNatLit 0))
      let system ← ProjectionProof.proof `AnalysisViewProjection.system
        (← mkAppM ``projectionSingletonSystemRedundant
          #[toExpr root, original, normalized, same, index, zero])
      let mut theorems := #[]
      for name in names, i in [:2] do
        let some loo := projection.leaveOneOut.find? (·.theoremName == qualified[i]!)
          | throwError "missing fixture leave-one-out"
        let certificateName := catalogQualifiedName root ``arena ``catalog name "__lowers_escape"
        let some (.thmDecl proof) := (← get).find? (·.getNames.contains loo.certificate)
          | throwError "missing fixture certificate"
        let _ ← ProjectionProof.proof certificateName proof.value
        let realizationName := catalogQualifiedName root ``arena ``catalog name
          primitiveRealizationSuffix
        let _ ← ProjectionProof.value realizationName
          (← mkConstWithFreshMVarLevels ``fixtureRealization)
        let bundle ← mkAppM ``TheoremUnit.primitives #[← mkConstWithFreshMVarLevels ``unit]
        let address ← unsafe evalExpr String (mkConst ``String)
          (← mkAppM ``primitiveKernelAddress #[← mkAppM ``Arena.stateFintype #[arena], bundle])
          (safety := .unsafe)
        theorems := theorems.push {
          theoremName := name, unitName := qualified[i]!,
          realizationName, certificateName, registrationModuleName := root, index := i,
          primitiveCount := 1, primitiveAxes := #["cut"], primitiveKernelAddress := address,
          uniqueCaptureCount := 0, fullEscapeCount := 0, withoutEscapeCount := 0,
          roleSignatureHistogram := #[], proofMethod := "reflected-readout" : SealTheoremRecord }
      let some verdict := projection.certificates.find? (·.1 == "verdict")
        | throwError "missing verdict"
      let counts : SealArenaRecord := {
        catalog := {
          rootId := root, catalogId := ``catalog, catalogKind := .analysisView,
          arenaName := ``arena, catalogName := ``catalog, compatibilityV2 := false,
          units := theorems.map fun row => {
            theoremName := row.theoremName,
            unitName := row.unitName, realizationName := row.realizationName,
            registrationModuleName := root, index := row.index } },
        irredundantCertificateName := verdict.2, proofMethod := "reflected-readout",
        stateCard := 2, offDiagonalPairCount := 2, fullEscapeCount := 0, theorems }
      let counts ← prepareV3QualifiedCounts counts (← get)
      pure ({ counts, projection, analysis, layerChains : V3CatalogRecord }, system)
      : ProjectionM _).run #[]
  for declaration in declarations do liftCoreM <| addDecl declaration
  let json ← liftTermElabM <| serializeV3Artifact root #[record] system
  let .ok artifact := Json.parse json | throwError "fixture JSON"
  let classes := (artifact.getObjValAs? (Array Json)
    "kernel_address_coincidence_classes").toOption.get!
  unless classes.size == 1 do throwError "nonempty coincidence fixture missing"
  let keys := classes[0]!.getObj?.toOption.get!.toArray.map (·.1) |>.qsort (· < ·)
  unless keys == #["diagnostic_only", "occurrences", "primitive_kernel_address", "serializer"] do
    throwError "nonempty coincidence key-set mismatch"
  let badCanonical := { record with counts := { record.counts with catalog := {
    record.counts.catalog with catalogKind := .canonicalMaximal } } }
  let duplicateRows := record.counts.theorems.map fun row => { row with theoremName := ``first }
  let badDuplicate := { record with counts := { record.counts with theorems := duplicateRows } }
  let mut messages := #[]
  for (label, candidate) in #[("redundant-canonical", badCanonical),
      ("duplicate-occurrence", badDuplicate),
      ("direct-route", { record with counts := { record.counts with proofMethod := "direct" } }),
      ("fused-route", { record with counts := {
        record.counts with proofMethod := "reflected-fused-counts" } }),
      ("native-route", { record with counts := {
        record.counts with proofMethod := "native_decide" } })] do
    let result ← try
      let _ ← liftTermElabM <| serializeV3Artifact root #[candidate] system
      pure "ACCEPTED"
    catch error =>
      let message ← error.toMessageData.toString
      pure ("rejected " ++ message)
    messages := messages.push (label ++ " " ++ result)
  messages := messages.push "nonempty coincidence key set passed"
  logInfo (String.intercalate "\n" messages.toList)

end LeanInformationAudit.Tests.Projection.AnalysisView
