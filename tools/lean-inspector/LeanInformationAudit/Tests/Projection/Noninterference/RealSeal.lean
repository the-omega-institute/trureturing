import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Occurrence.ImportClosureProducer
import LeanInformationAudit.Tests.Projection.FixtureState

/-!
T-041 production-command fixture. Negative runs select publication or export audit
rejection, export before staging, or staging before seal. Each requires an exact
diagnostic, unchanged declarations, and absent artifacts. The control seals once,
stages once, and exports twice to distinct paths with byte-identical results.

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
  let sealArtifact := Syntax.mkStrLit paths[0]!
  let analysis := Syntax.mkStrLit paths[1]!
  let ascii := Syntax.mkStrLit paths[2]!
  `(command| #export_information_analysis root $rootId:ident output $sealArtifact:str
    analysis_output $analysis:str ascii_output $ascii:str)

private def stageSyntax (root : Name) : CommandElabM Syntax := do
  let rootId := mkIdent (`_root_ ++ root)
  `(command| #stage_information_analysis root $rootId:ident)

run_cmd do
  let expectedSeal ← liftIO <| IO.getEnv "IE_EXPECT_SEAL_REJECTION"
  let expectedStage ← liftIO <| IO.getEnv "IE_EXPECT_STAGE_REJECTION"
  let expectedExport ← liftIO <| IO.getEnv "IE_EXPECT_EXPORT_REJECTION"
  let exportBeforeSeal ← liftIO <| IO.getEnv "IE_EXPORT_BEFORE_SEAL"
  let exportBeforeStage ← liftIO <| IO.getEnv "IE_EXPORT_BEFORE_STAGE"
  let stageBeforeSeal ← liftIO <| IO.getEnv "IE_STAGE_BEFORE_SEAL"
  let firstPaths ← #["real-seal.json", "real-analysis.json", "real-ascii.txt"].mapM fixturePath
  let secondPaths ←
    #["repeat-seal.json", "repeat-analysis.json", "repeat-ascii.txt"].mapM fixturePath
  assertArtifactsAbsent (firstPaths ++ secondPaths)
  let beforeSeal ← getEnv
  let root := beforeSeal.header.mainModule

  if stageBeforeSeal.isSome then
    let expected := s!"UnsealedAnalysisStage root={root} catalog=system"
    let errors ← commandErrors (← stageSyntax root)
    unless errors == #[expected] do
      throwError "RealSeal expected unsealed stage rejection {expected}; actual={errors}"
    assertNoNewDeclarations beforeSeal (← getEnv)
    unless (SealRecords.analysisForRoot? (← getEnv) root).isNone do
      throwError "RealSeal unsealed stage published records"
    assertArtifactsAbsent firstPaths
    logInfo s!"RealSeal rejected stage before seal: {expected}"
    return

  if exportBeforeSeal.isSome then
    let expected := s!"UnstagedAnalysisExport root={root} catalog=system"
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
  unless SealRecords.systemCatalogIrredundant sealedEnv root do
    throwError "RealSeal seal publication missing"
  if (SealRecords.analysisForRoot? sealedEnv root).isSome ||
      sealedEnv.contains (root.str "__system_catalog_irredundant") then
    throwError "RealSeal seal published analysis staging"

  if exportBeforeStage.isSome then
    let expected := s!"UnstagedAnalysisExport root={root} catalog=system"
    let errors ← commandErrors (← exportSyntax root firstPaths)
    unless errors == #[expected] do
      throwError "RealSeal expected unstaged export rejection {expected}; actual={errors}"
    assertNoNewDeclarations sealedEnv (← getEnv)
    unless (SealRecords.analysisForRoot? (← getEnv) root).isNone do
      throwError "RealSeal unstaged export published records"
    assertArtifactsAbsent firstPaths
    logInfo s!"RealSeal rejected export before stage: {expected}"
    return

  let stageErrors ← commandErrors (← stageSyntax root)
  match expectedStage with
  | some expected =>
      unless stageErrors == #[expected] do
        throwError "RealSeal expected stage rejection {expected}; actual={stageErrors}"
      assertNoNewDeclarations sealedEnv (← getEnv)
      unless (SealRecords.analysisForRoot? (← getEnv) root).isNone do
        throwError "RealSeal rejected stage published records"
      assertArtifactsAbsent firstPaths
      logInfo s!"RealSeal stage rejected before publication and writes: {expected}"
      return
  | none =>
      unless stageErrors.isEmpty do throwError "RealSeal stage failed: {stageErrors}"
  let stagedEnv ← getEnv
  unless stagedEnv.contains (root.str "__system_catalog_irredundant") &&
      (SealRecords.analysisForRoot? stagedEnv root).isSome do
    throwError "RealSeal analysis publication missing"

  let exportErrors ← commandErrors (← exportSyntax root firstPaths)
  match expectedExport with
  | some expected =>
      unless exportErrors == #[expected] do
        throwError "RealSeal expected export rejection {expected}; actual={exportErrors}"
      assertNoNewDeclarations stagedEnv (← getEnv)
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
      assertNoNewDeclarations stagedEnv (← getEnv)
      logInfo "RealSeal staged once and exported byte-identical artifacts twice"
