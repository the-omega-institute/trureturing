import LeanInformationAudit.ProjectionSeal
import D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalCatalog
import LeanInformationAudit.Tests.Projection.FixtureState

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment
open D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalCatalog

namespace LeanInformationAudit.Tests.Projection.Causal

local instance : DecidableEq ObsOut := projectionSumDecision
local instance : DecidableEq IntOut := projectionSumDecision
local instance : DecidableEq CfOut := projectionSumDecision

def readoutArena {Output : Type} [DecidableEq Output]
    (readout : UnifiedBoolSCM → Output) : PrimitiveLawArena where
  toArena := unifiedArena
  signature := {
    Index := Fin 1, indexFintype := inferInstance, indexDecidableEq := inferInstance,
    Output := fun _ => Output, outputDecidableEq := fun _ => inferInstance,
    axis := fun _ => .cut, readoutAxisNotAnchor := by simp,
    AnchorIndex := Fin 0, anchorFintype := inferInstance, anchorDecidableEq := inferInstance }
  Law := fun realization => realization.readout 0 = readout

def readoutRealization {Output : Type} [DecidableEq Output]
    (readout : UnifiedBoolSCM → Output) :
    PrimitiveRealization (readoutArena readout).signature where
  readout := fun _ => readout
  anchor := Fin.elim0

def counterfactualRealization := readoutRealization CfU
def interventionRealization := readoutRealization IntU
def observationRealization := readoutRealization ObsU
theorem counterfactualOccurrence : (readoutArena CfU).Law counterfactualRealization := rfl
theorem interventionOccurrence : (readoutArena IntU).Law interventionRealization := rfl
theorem observationOccurrence : (readoutArena ObsU).Law observationRealization := rfl
def counterfactualUnit : TheoremUnit unifiedArena := NativeTheoremUnit.toTheoremUnit
  (arena := readoutArena CfU) ⟨counterfactualRealization, counterfactualOccurrence⟩
def interventionUnit : TheoremUnit unifiedArena := NativeTheoremUnit.toTheoremUnit
  (arena := readoutArena IntU) ⟨interventionRealization, interventionOccurrence⟩
def observationUnit : TheoremUnit unifiedArena := NativeTheoremUnit.toTheoremUnit
  (arena := readoutArena ObsU) ⟨observationRealization, observationOccurrence⟩

abbrev catalog : Catalog unifiedArena := Catalog.ofVector
  ![counterfactualUnit, interventionUnit, observationUnit]

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

run_cmd do
  let occurrenceNames := #[``counterfactualOccurrence, ``interventionOccurrence, ``observationOccurrence]
  let qualified := occurrenceNames.map fun name =>
    catalogQualifiedName `Causal ``unifiedArena ``catalog name theoremUnitSuffix
  let ((projection, analysis, layers), declarations) ← liftTermElabM do
    (prepareKernelProjection (← mkConstWithFreshMVarLevels ``catalog)
      (← mkConstWithFreshMVarLevels ``unifiedArena)
      qualified
      `Causal ``catalog ``unifiedArena `CausalProjection {
        schedules := #[("obs-int-cf", #[2, 1, 0])]
      }).run #[]
  unless projection.nodes.size == 4 do throwError "causal quotient size"
  unless projection.denominator == 2256 do throwError "causal denominator"
  unless projection.certifiedChains.size == 1 do throwError "causal schedule count"
  let chain := projection.certifiedChains[0]!
  let mut escapeCounts := #[]
  for key in chain.nodes do
    let some node := projection.nodes.find? (·.key == key)
      | throwError "causal unresolved schedule node"
    escapeCounts := escapeCounts.push node.escapeCount
  unless escapeCounts == #[2256, 136, 44, 0] do
    throwError "causal escape counts: {escapeCounts}"
  unless chain.increments == #[2120, 92, 44] do
    throwError "causal increments: {chain.increments}"
  unless chain.stepClasses == #["strict", "strict", "strict"] do
    throwError "causal step classifications"
  unless chain.terminalEscapeCount == 0 do throwError "causal terminal escape"
  unless layers.map (·.layers.map (·.count)) == #[#[0, 2120, 92, 44]] do
    throwError "causal layered captures"
  for (theoremName, expected) in #[
      (qualified[2]!, 0), (qualified[1]!, 0), (qualified[0]!, 44)] do
    let some row := projection.leaveOneOut.find? (·.theoremName == theoremName)
      | throwError "causal missing leave-one-out row"
    unless row.uniqueCaptureCount == expected do
      throwError "causal leave-one-out count for {theoremName}: {row.uniqueCaptureCount}"
  unless projection.verdict == "redundant" do throwError "causal catalog verdict"
  unless projection.edges.size == 6 do throwError "causal strict transition count"
  let covers := projection.edges.filter (·.isCover)
  unless covers.size == 3 do throwError "causal cover count"
  unless (covers.map (·.captureCount)).qsort (· < ·) == #[44, 92, 2120] do
    throwError "causal cover capture counts"
  for declaration in declarations do
    liftCoreM <| addDecl declaration
    for name in declaration.getNames do
      elabCommand (← `(command| #print axioms $(mkIdent name)))
  let .ok ascii := renderAsciiHierarchy `Causal ``catalog ``unifiedArena projection
    | throwError "causal renderer"
  unless ((ascii.splitOn "\n").filter (·.startsWith "  +--[")).length == 3 do
    throwError "causal ASCII cover count"
  let candidate := { projection with verdict := "irredundant" }
  let .error message := validateProjectionSnapshot `Causal ``catalog projection candidate
    | throwError "causal verdict mutation accepted"
  unless message.startsWith "IE-C042 KernelProjectionCertificateMismatch" do
    throwError "causal verdict mutation classification"
  let ((record, system), countDeclarations) ← liftTermElabM do
    (do
      let original ← mkConstWithFreshMVarLevels ``catalog
      let arena ← mkConstWithFreshMVarLevels ``unifiedArena
      let (normalized, same) ← ProjectionProof.reflectCatalog original 3
      let index ← ProjectionProof.fin 1 3
      let zero ← mkDecideProof (← mkEq
        (← mkAppM ``Catalog.uniqueCaptureCount #[normalized, index]) (mkNatLit 0))
      let system ← ProjectionProof.proof `CausalProjection.system
        (← mkAppM ``projectionSingletonSystemRedundant
          #[toExpr (`Causal : Name), original, normalized, same, index, zero])
      let names := #[``counterfactualUnit, ``interventionUnit, ``observationUnit]
      let realizations := #[``counterfactualRealization, ``interventionRealization, ``observationRealization]
      let mut theorems := #[]
      let moduleName := (← getEnv).header.mainModule
      for unitName in names, i in [:3] do
        let unit ← mkAppM ``Catalog.theoremAt #[normalized, ← ProjectionProof.fin i 3]
        let bundle ← mkAppM ``TheoremUnit.primitives #[unit]
        let address ← primitiveKernelAddress (← mkAppM ``Arena.stateFintype #[arena]) bundle
        let some row := projection.leaveOneOut.find? (·.theoremName == qualified[i]!)
          | throwError "causal missing occurrence"
        let mut roles := #[]
        for mask in [1:16] do
          let bits := (Array.range 4).map fun bit => mask / 2 ^ (3 - bit) % 2 == 1
          let signature ← ProjectionProof.vector
            (bits.map fun bit => mkConst (if bit then ``Bool.true else ``Bool.false))
          let expression ← mkAppM ``Catalog.roleHistogram
            #[normalized, ← ProjectionProof.fin i 3, signature]
          let (count, _) ← ProjectionProof.count
            ((`CausalProjection).str s!"role_{i}_{mask}") expression
          if count > 0 then
            roles := roles.push
              (String.ofList (bits.toList.map fun bit => if bit then '1' else '0'), count)
        theorems := theorems.push {
          theoremName := occurrenceNames[i]!, unitName, realizationName := realizations[i]!,
          certificateName := row.certificate, registrationModuleName := moduleName,
          index := i, primitiveCount := 1, primitiveAxes := #["cut"],
          primitiveKernelAddress := address, uniqueCaptureCount := row.uniqueCaptureCount,
          fullEscapeCount := chain.terminalEscapeCount,
          withoutEscapeCount := row.uniqueCaptureCount + chain.terminalEscapeCount,
          roleSignatureHistogram := roles, proofMethod := "reflected-readout" : SealTheoremRecord }
      let some verdict := projection.certificates.find? (·.1 == "verdict")
        | throwError "causal missing verdict certificate"
      let counts : SealArenaRecord := {
        catalog := {
          rootId := `Causal, catalogId := ``catalog, catalogKind := .analysisView,
          arenaName := ``unifiedArena, catalogName := ``catalog,
          compatibilityV2 := false, units := theorems.map fun row => {
            theoremName := row.theoremName, unitName := row.unitName,
            realizationName := row.realizationName, registrationModuleName := moduleName,
            index := row.index } },
        irredundantCertificateName := verdict.2, proofMethod := "reflected-readout",
        stateCard := 48, offDiagonalPairCount := projection.denominator,
        fullEscapeCount := chain.terminalEscapeCount, theorems }
      let counts ← prepareV3QualifiedCounts counts (← get)
      pure ({ counts, projection, analysis, layerChains := layers : V3CatalogRecord }, system)
      : ProjectionM _).run #[]
  for declaration in countDeclarations do
    liftCoreM <| addDecl declaration
    for name in declaration.getNames do
      elabCommand (← `(command| #print axioms $(mkIdent name)))
  let json ← liftTermElabM <| serializeV3Artifact `Causal #[record] system
  let .ok artifact := Json.parse json | throwError "causal v3 JSON"
  unless (artifact.getObjValAs? Bool "system_catalog_irredundant").toOption == some false do
    throwError "causal system verdict"
  liftIO <| IO.FS.writeFile (← fixturePath "causal-v3.json") json
  liftIO <| IO.FS.writeFile (← fixturePath "causal-v3.txt") ascii

#print axioms catalog

end LeanInformationAudit.Tests.Projection.Causal
