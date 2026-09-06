import D5.S3.ConceptDynamics.InformationEscape.InformationRoot
import LeanInformationAudit.ProjectionSeal
import LeanInformationAudit.Tests.Projection.FixtureState

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Projection.FrozenRootV3

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

run_cmd do
  let root := frozenInformationRootId
  let counts := SealRecords.forRoot (← getEnv) root
  unless counts.size == 11 do throwError "frozen root arena inventory"
  let observed := counts.flatMap (·.theorems.map (·.uniqueCaptureCount))
  unless observed.qsort (· < ·) == (#[570, 12, 20, 56, 240, 968, 6, 12, 48, 60, 2]).qsort
      (· < ·) do throwError "frozen root reseal counts: {observed}"
  let v2 := serializeV2Artifact counts
  unless Sha256.hex v2.toUTF8 ==
      "6da462e5cbfa01261eb820dd4c236f647632fd36fe8df9a391ec5ed9800cd16b" do
    throwError "frozen root v2 digest"
  let ((records, system), declarations) ← liftTermElabM do
    (do
      let mut records := #[]
      let mut packed := #[]
      for count in counts, i in [:counts.size] do
        let count ← prepareV3QualifiedCounts count #[]
        let metadata := count.catalog
        let catalogValue ← mkConstWithFreshMVarLevels metadata.catalogName
        let arena ← mkAppM ``PrimitiveLawArena.toArena
          #[← mkConstWithFreshMVarLevels metadata.arenaName]
        let (projection, analysis, layerChains) ← prepareKernelProjection catalogValue arena
          (metadata.units.map (·.unitName)) root metadata.catalogId metadata.arenaName
          ((`LeanInformationAudit.Tests.Projection.FrozenRootV3).str s!"arena_{i}")
        records := records.push { counts := count, projection, analysis, layerChains : V3CatalogRecord }
        for row in count.theorems do
          unless row.unitName == catalogQualifiedName root metadata.arenaName metadata.catalogId
              row.theoremName theoremUnitSuffix &&
              row.certificateName == catalogQualifiedName root metadata.arenaName metadata.catalogId
              row.theoremName "__lowers_escape" do
            throwError "frozen root v3 identities are unqualified"
        packed := packed.push (← mkAppM ``PackedCatalog.mk #[arena, catalogValue])
      let family ← ProjectionProof.vector packed
      let suite ← mkAppM ``projectionSuite #[toExpr root, family]
      let proposition ← mkAppM ``SystemCatalogIrredundant #[suite]
      let decision ← mkAppM ``projectionSystemDecidable #[toExpr root, family]
      let evidence ← mkAppOptM ``of_decide_eq_true #[some proposition, some decision,
        some (← mkEqRefl (mkConst ``Bool.true))]
      let system ← ProjectionProof.proof
        `LeanInformationAudit.Tests.Projection.FrozenRootV3.system evidence
      pure (records, system) : ProjectionM _).run #[]
  for declaration in declarations do
    liftCoreM <| addDecl declaration
    for name in declaration.getNames do
      elabCommand (← `(command| #print axioms $(mkIdent name)))
  let json ← liftTermElabM <| serializeV3Artifact root records system
  let .ok ascii := serializeAsciiArtifact records | throwError "frozen root ASCII"
  let .ok artifact := Json.parse json | throwError "frozen root JSON"
  unless (artifact.getObjValAs? (Array Json) "catalogs").toOption.map (·.size) == some 11 do
    throwError "frozen root v3 arena inventory"
  liftIO <| IO.FS.writeFile (← fixturePath "frozen-v3.json") json
  liftIO <| IO.FS.writeFile (← fixturePath "frozen-v3.txt") ascii
  liftIO <| IO.FS.writeFile (← fixturePath "frozen-v2.json") v2
  logInfo m!"frozen root v3: 11 arenas; unique counts {observed}"

end LeanInformationAudit.Tests.Projection.FrozenRootV3
