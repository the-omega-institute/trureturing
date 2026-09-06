import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Occurrence.ImportClosureProducer
import LeanInformationAudit.Tests.Projection.FixtureState

/-!
T-041 production-command fixture. Negative runs select one of three boundaries:
seal audit rejection, export audit rejection, or export before seal. Every negative
case requires an exact diagnostic, an unchanged declaration environment, and no
artifact. The unmodified control seals once and exports twice to distinct paths;
the two artifact sets must be byte-identical.

Structural boundary: `#seal_information_theory` contains no destination syntax and
its audited publication closure cannot read the current command reference. The
separate export reads retained seal/projection records and is audited against
environment mutation before it may enter terminal IO. The owned-definition audit
also rejects direct IO/System/Lean.FS capabilities and the enumerated Lean-core
module loaders. External Lean/Init/Std/Mathlib bodies remain opaque; this is not an
OS sandbox or a full-core purity claim.
-/

open Lean Lean.Elab.Command LeanInformationAudit
open LeanInformationAudit.Tests.ImportClosureProducer
open LeanInformationAudit.Tests.Projection

expect_information_occurrence importedTheorem
  in objectArena
  from "LeanInformationAudit.Tests.Occurrence.ImportClosureProducer"

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

private def commandErrors (command : Syntax) : CommandElabM (Array String) := do
  let savedMessages := (← get).messages
  modify fun state => { state with messages := {} }
  elabCommand command
  let errors := (← get).messages.toArray.filter (·.severity == .error)
  let errorMessages ← errors.mapM (·.data.toString)
  modify fun state => { state with messages := savedMessages }
  pure errorMessages

private def assertNoNewDeclarations (before after : Environment) : CommandElabM Unit := do
  for (name, _) in after.constants.toList do
    unless before.contains name do
      throwError "RealSeal rejected but published declaration {name}"

private def assertArtifactsAbsent (paths : Array String) : CommandElabM Unit := do
  for path in paths do
    if ← liftIO <| (System.FilePath.mk path).pathExists then
      throwError "RealSeal rejection wrote artifact {path}"

private def exportSyntax (root : Name) (paths : Array String) : CommandElabM Syntax := do
  let rootId := mkIdent (`_root_ ++ root)
  let v2 := Syntax.mkStrLit paths[0]!
  let v3 := Syntax.mkStrLit paths[1]!
  let ascii := Syntax.mkStrLit paths[2]!
  `(command| #export_information_analysis root $rootId:ident output $v2:str
    analysis_output $v3:str ascii_output $ascii:str)

run_cmd do
  let expectedSeal ← liftIO <| IO.getEnv "IE_EXPECT_SEAL_REJECTION"
  let expectedExport ← liftIO <| IO.getEnv "IE_EXPECT_EXPORT_REJECTION"
  let exportBeforeSeal ← liftIO <| IO.getEnv "IE_EXPORT_BEFORE_SEAL"
  let firstPaths ← #["real-v2.json", "real-v3.json", "real-ascii.txt"].mapM fixturePath
  let secondPaths ← #["repeat-v2.json", "repeat-v3.json", "repeat-ascii.txt"].mapM fixturePath
  assertArtifactsAbsent (firstPaths ++ secondPaths)
  let beforeSeal ← getEnv
  let root := beforeSeal.header.mainModule

  if exportBeforeSeal.isSome then
    let expected := s!"IE-C044 UnsealedAnalysisExport root={root} catalog=system"
    let errors ← commandErrors (← exportSyntax root firstPaths)
    unless errors == #[expected] do
      throwError "RealSeal expected unsealed export rejection {expected}; actual={errors}"
    assertNoNewDeclarations beforeSeal (← getEnv)
    assertArtifactsAbsent firstPaths
    logInfo s!"RealSeal rejected export before seal: {expected}"
    return

  let sealErrors ← commandErrors (← `(command| #seal_information_theory))
  match expectedSeal with
  | some expected =>
      unless sealErrors == #[expected] do
        throwError "RealSeal expected seal rejection {expected}; actual={sealErrors}"
      let after ← getEnv
      unless (SealRecords.forRoot after root).isEmpty do
        throwError "RealSeal rejected but published seal records"
      assertNoNewDeclarations beforeSeal after
      assertArtifactsAbsent firstPaths
      logInfo s!"RealSeal seal rejected before publication and writes: {expected}"
      return
  | none =>
      unless sealErrors.isEmpty do throwError "RealSeal seal failed: {sealErrors}"

  let sealedEnv ← getEnv
  unless sealedEnv.contains (root.str "__system_catalog_irredundant") &&
      SealRecords.systemCatalogIrredundant sealedEnv root do
    throwError "RealSeal seal publication missing"

  let exportErrors ← commandErrors (← exportSyntax root firstPaths)
  match expectedExport with
  | some expected =>
      unless exportErrors == #[expected] do
        throwError "RealSeal expected export rejection {expected}; actual={exportErrors}"
      assertNoNewDeclarations sealedEnv (← getEnv)
      assertArtifactsAbsent firstPaths
      logInfo s!"RealSeal export rejected before writes: {expected}"
  | none =>
      unless exportErrors.isEmpty do throwError "RealSeal export failed: {exportErrors}"
      let repeatedErrors ← commandErrors (← exportSyntax root secondPaths)
      unless repeatedErrors.isEmpty do
        throwError "RealSeal repeated export failed: {repeatedErrors}"
      for (first, second) in firstPaths.zip secondPaths do
        let firstContents ← liftIO <| IO.FS.readFile first
        let secondContents ← liftIO <| IO.FS.readFile second
        if firstContents.isEmpty then throwError "RealSeal empty artifact {first}"
        unless firstContents == secondContents do
          throwError "RealSeal nondeterministic export: {first} != {second}"
      logInfo "RealSeal sealed once and exported byte-identical artifacts twice"
