import LeanInformationAudit.Tests.Projection.Noninterference.SealedRoot
import LeanInformationAudit.Tests.Projection.FixtureState

/-!
The selected root was sealed in another module. The mutation runner requires exact
stage/export diagnostics naming that root, with no declarations or artifacts
published on rejection. The control stages and exports the imported root.
-/

open Lean Lean.Elab.Command LeanInformationAudit
open LeanInformationAudit.Tests.Projection

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
      throwError "ImportedRoot rejected but published declaration {name}"

private def assertArtifactsAbsent (paths : Array String) : CommandElabM Unit := do
  for path in paths do
    if ← liftIO <| (System.FilePath.mk path).pathExists then
      throwError "ImportedRoot rejection wrote artifact {path}"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Analysis staging constructs and checks the full certificate family in one command.
run_cmd do
  let expectedStage ← liftIO <| IO.getEnv "IE_EXPECT_STAGE_REJECTION"
  let expectedExport ← liftIO <| IO.getEnv "IE_EXPECT_EXPORT_REJECTION"
  let paths ← #["imported-seal.json", "imported-analysis.json", "imported-ascii.txt"].mapM
    fixturePath
  assertArtifactsAbsent paths
  let root := `LeanInformationAudit.Tests.Projection.Noninterference.SealedRoot
  let sealedEnv ← getEnv
  if sealedEnv.header.mainModule == root then
    throwError "ImportedRoot must audit a root from another module"
  unless SealRecords.systemCatalogIrredundant sealedEnv root do
    throwError "ImportedRoot missing imported seal"
  unless (SealRecords.analysisForRoot? sealedEnv root).isNone do
    throwError "ImportedRoot was staged before import"
  -- Exercise both accepted root spellings; _root_ must not enter the diagnostic.
  let rootIds := #[mkIdent root, mkIdent (`_root_ ++ root)]
  for rootId in rootIds do
    let errors ← commandErrors (← `(command| #stage_information_analysis root $rootId:ident))
    match expectedStage with
    | some expected =>
        unless errors == #[expected] do
          throwError "ImportedRoot expected stage rejection {expected}; actual={errors}"
        assertNoNewDeclarations sealedEnv (← getEnv)
        unless (SealRecords.analysisForRoot? (← getEnv) root).isNone do
          throwError "ImportedRoot rejected stage published records"
        assertArtifactsAbsent paths
        logInfo s!"ImportedRoot stage rejected before publication and writes: {expected}"
    | none =>
        unless errors.isEmpty do throwError "ImportedRoot stage failed: {errors}"
        break
  if expectedStage.isSome then return
  let stagedEnv ← getEnv
  unless stagedEnv.contains (root.str "__system_catalog_irredundant") &&
      (SealRecords.analysisForRoot? stagedEnv root).isSome do
    throwError "ImportedRoot analysis publication missing"
  unless (SealRecords.analysisForRoot? stagedEnv stagedEnv.header.mainModule).isNone do
    throwError "ImportedRoot staged the caller instead of the selected root"
  let sealArtifact := Syntax.mkStrLit paths[0]!
  let analysis := Syntax.mkStrLit paths[1]!
  let ascii := Syntax.mkStrLit paths[2]!
  for rootId in rootIds do
    let errors ← commandErrors (← `(command| #export_information_analysis root $rootId:ident
      output $sealArtifact:str analysis_output $analysis:str ascii_output $ascii:str))
    match expectedExport with
    | some expected =>
        unless errors == #[expected] do
          throwError "ImportedRoot expected export rejection {expected}; actual={errors}"
        assertNoNewDeclarations stagedEnv (← getEnv)
        assertArtifactsAbsent paths
        logInfo s!"ImportedRoot export rejected before writes: {expected}"
    | none =>
        unless errors.isEmpty do throwError "ImportedRoot export failed: {errors}"
        for path in paths do
          if (← liftIO <| IO.FS.readFile path).isEmpty then
            throwError "ImportedRoot empty artifact {path}"
        assertNoNewDeclarations stagedEnv (← getEnv)
  if expectedExport.isNone then
    logInfo "ImportedRoot staged and exported the imported sealed root"
