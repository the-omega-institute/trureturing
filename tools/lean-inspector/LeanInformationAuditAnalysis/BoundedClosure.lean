import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import LeanInformationAudit.Projection.ProjectionSeal
import LeanInformationAudit.Tests.Projection.FixtureState

/-!
This full-analysis fixture belongs to `LeanInformationAuditAnalysis` and stays
outside every default Lake target because of its cost: approximately 289-367 s
single-module elaboration on a 28-core Apple Silicon host with warm mathlib/project
caches (attempt-1 runs: 367 s / 289 s; measured 2026-09-07).
Build it with `lake build LeanInformationAuditAnalysis` after
`make lean-cache-ensure`. Use `run-analysis-fixtures.sh OUTPUT_DIRECTORY` to rebuild
the analysis modules and hash their artifacts, including on a warm build.
It writes `bounded-analysis.json` and `bounded-analysis.txt` under
`IE_PROJECTION_OUTPUT_DIR`, or a fresh temporary directory when unset.
-/

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit
open LeanInformationAudit.Tests.Projection
open D5.S3.ConceptDynamics.InformationEscape D5.S3.ConceptDynamics.CIRPT

namespace BoundedClosure

def arena : Arena := Arena.ofFintype (Fin 9)
def unit (coordinate : Nat) : TheoremUnit arena := {
  primitives := {
    Index := Fin 1, indexFintype := inferInstance, indexDecidableEq := inferInstance,
    atom := fun _ => ⟨.cut, cutKernel (fun state : Fin 9 => state.val == coordinate)⟩ }
  Statement := True, proof := True.intro }
def catalog : Catalog arena := Catalog.ofVector (fun i : Fin 16 => unit (i.val / 2))

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

/-- info: duplicate bottom: eight generators, zero subset visits -/
#guard_msgs in
run_cmd do
  let names := #[`g00, `g01, `g02, `g03, `g04, `g05, `g06, `g07,
    `g08, `g09, `g10, `g11, `g12, `g13, `g14, `g15]
  let (selected, work) ← liftTermElabM do
    canonicalSelectionWork (← mkConstWithFreshMVarLevels ``catalog) names (Array.range 16)
  unless selected == #[0, 2, 4, 6, 8, 10, 12, 14] && work == 0 do
    throwError "duplicate bottom selected={selected} subset-visits={work}"
  logInfo "duplicate bottom: eight generators, zero subset visits"

def triangleArena : Arena := Arena.ofFintype (Fin 3)
def triangleUnit (coordinate : Fin 3) : TheoremUnit triangleArena := {
  primitives := {
    Index := Fin 1, indexFintype := inferInstance, indexDecidableEq := inferInstance,
    atom := fun _ => ⟨.cut, cutKernel (fun state : Fin 3 => state == coordinate)⟩ }
  Statement := True, proof := True.intro }
def triangle : Catalog triangleArena := Catalog.ofVector triangleUnit

/-- info: nonessential bottom: canonical pair from closure clauses -/
#guard_msgs in
run_cmd do
  let (selected, work) ← liftTermElabM do
    canonicalSelectionWork (← mkConstWithFreshMVarLevels ``triangle) #[`c, `a, `b] #[0, 1, 2]
  unless selected == #[1, 2] && work == 0 do throwError "nonessential closure {selected} {work}"
  logInfo "nonessential bottom: canonical pair from closure clauses"

def lawArena : PrimitiveLawArena where
  toArena := arena
  signature := {
    Index := Fin 1, indexFintype := inferInstance, indexDecidableEq := inferInstance,
    Output := fun _ => Bool, outputDecidableEq := fun _ => inferInstance,
    axis := fun _ => .cut, readoutAxisNotAnchor := by simp,
    AnchorIndex := Fin 0, anchorFintype := inferInstance, anchorDecidableEq := inferInstance }
  Law := fun _ => True
def realization (coordinate : Nat) : PrimitiveRealization lawArena.signature where
  readout := fun _ state => state.val == coordinate
  anchor := Fin.elim0
def nativeUnit (coordinate : Nat) : TheoremUnit arena := NativeTheoremUnit.toTheoremUnit
  (arena := lawArena) ⟨realization coordinate, True.intro⟩
def viewCatalog : Catalog arena := Catalog.ofVector (fun i : Fin 16 => nativeUnit (i.val / 2))

/-- info: duplicate analysis view serialized: 16 occurrences, 9 nodes, complete=false -/
#guard_msgs in
run_cmd do
  let root := `BoundedClosure
  let moduleName := (← getEnv).header.mainModule
  let names := #[`g00, `g01, `g02, `g03, `g04, `g05, `g06, `g07,
    `g08, `g09, `g10, `g11, `g12, `g13, `g14, `g15].map (root ++ ·)
  let qualified := names.map fun name =>
    catalogQualifiedName root ``arena ``viewCatalog name theoremUnitSuffix
  let ((record, system), declarations) ← liftTermElabM do
    (do
      let original ← mkConstWithFreshMVarLevels ``viewCatalog
      let arenaValue ← mkConstWithFreshMVarLevels ``arena
      for name in names, unitName in qualified, i in [:16] do
        let _ ← ProjectionProof.proof name (mkConst ``True.intro)
        let unit ← mkAppM ``nativeUnit #[mkNatLit (i / 2)]
        let _ ← ProjectionProof.value unitName unit
      let (projection, analysis, layerChains) ← prepareKernelProjection
        original arenaValue qualified root ``viewCatalog ``arena `DuplicateView
      unless projection.nodes.size == 9 && !projection.completeLatticeMaterialized do
        throwError "duplicate mandatory node coverage"
      let (normalized, same) ← ProjectionProof.reflectCatalog original 16
      let index ← ProjectionProof.fin 0 16
      let zero ← mkDecideProof (← mkEq
        (← mkAppM ``Catalog.uniqueCaptureCount #[normalized, index]) (mkNatLit 0))
      let system ← ProjectionProof.proof `DuplicateView.system
        (← mkAppM ``projectionSingletonSystemRedundant
          #[toExpr root, original, normalized, same, index, zero])
      let mut theorems := #[]
      for name in names, i in [:16] do
        let some _loo := projection.leaveOneOut.find? (·.theoremName == qualified[i]!)
          | throwError "missing duplicate leave-one-out"
        let certificateName := catalogQualifiedName root ``arena ``viewCatalog name
          "__trivial_in_catalog"
        let position ← ProjectionProof.fin i 16
        let emptyIff ← mkAppOptM ``Finset.card_eq_zero
          #[none, some (← mkAppM ``Catalog.uniqueCapturePairs #[original, position])]
        let zero ← mkDecideProof (← mkEq
          (← mkAppM ``Catalog.uniqueCaptureCount #[original, position]) (mkNatLit 0))
        let _ ← ProjectionProof.proof certificateName (← mkAppM ``Iff.mp #[emptyIff, zero])
        let realizationName := catalogQualifiedName root ``arena ``viewCatalog name
          primitiveRealizationSuffix
        let _ ← ProjectionProof.value realizationName
          (← mkAppM ``realization #[mkNatLit (i / 2)])
        let bundle ← mkAppM ``TheoremUnit.primitives
          #[← mkAppM ``nativeUnit #[mkNatLit (i / 2)]]
        let address ← primitiveKernelAddress (← mkAppM ``Arena.stateFintype #[arenaValue]) bundle
        theorems := theorems.push {
          theoremName := name, unitName := qualified[i]!, realizationName,
          certificate := .trivial certificateName,
          registrationModuleName := moduleName, index := i, primitiveCount := 1,
          primitiveAxes := #["cut"], primitiveKernelAddress := address,
          uniqueCaptureCount := 0, fullEscapeCount := 0, withoutEscapeCount := 0,
          roleSignatureHistogram := #[], proofMethod := "reflected-readout" : SealTheoremRecord }
      let verdictType ← mkAppM ``Catalog.CatalogRedundant #[original]
      let predicate := (← whnf verdictType).appArg!
      let zero ← mkDecideProof (← mkEq
        (← mkAppM ``Catalog.uniqueCaptureCount #[original, index]) (mkNatLit 0))
      let verdict ← ProjectionProof.proof `DuplicateView.catalogRedundant
        (← mkAppOptM ``Exists.intro #[none, some predicate, some index, some zero])
      let counts : SealArenaRecord := {
        catalog := {
          rootId := root, catalogId := ``viewCatalog, catalogKind := .analysisView,
          arenaName := ``arena, catalogName := ``viewCatalog, localSealNames := false,
          units := theorems.map fun row => {
            theoremName := row.theoremName, unitName := row.unitName,
            realizationName := row.realizationName, registrationModuleName := moduleName,
            index := row.index } },
        verdict := .redundant verdict, proofMethod := "reflected-readout",
        stateCard := 9, offDiagonalPairCount := 72, fullEscapeCount := 0, theorems }
      let counts ← prepareAnalysisQualifiedCounts counts (← get)
      pure ({ counts, projection, analysis, layerChains : AnalysisCatalogRecord }, system)
      : ProjectionM _).run #[]
  for declaration in declarations do liftCoreM <| addDecl declaration
  let json ← liftTermElabM <| serializeAnalysisArtifact root #[record] system
  let .ok artifact := Json.parse json | throwError "duplicate view JSON"
  let rows := (artifact.getObjValAs? (Array Json) "catalogs").toOption.get!
  unless rows.size == 1 do throwError "duplicate view missing catalog"
  let .ok ascii := serializeAsciiArtifact #[record] | throwError "duplicate view ASCII"
  liftIO <| IO.FS.writeFile (← fixturePath "bounded-analysis.json") json
  liftIO <| IO.FS.writeFile (← fixturePath "bounded-analysis.txt") ascii
  logInfo "duplicate analysis view serialized: 16 occurrences, 9 nodes, complete=false"

end BoundedClosure
