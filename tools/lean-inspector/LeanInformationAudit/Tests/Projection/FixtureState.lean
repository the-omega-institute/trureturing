import LeanInformationAudit.Projection.ProjectionSchema

namespace LeanInformationAudit.Tests.Projection

open Lean Lean.Elab.Command

/-- The runner supplies a unique directory; interactive runs get a fresh temporary directory. -/
initialize fixtureDirectory : IO.Ref (Option System.FilePath) ← IO.mkRef none

def fixturePath (file : String) : Lean.Elab.Command.CommandElabM String := do
  let directory ← liftIO do
    if let some directory ← fixtureDirectory.get then return directory
    let directory ← match ← IO.getEnv "IE_PROJECTION_OUTPUT_DIR" with
      | some path => pure (System.FilePath.mk path)
      | none => do
        let temporary ← IO.FS.createTempDir
        pure temporary
    IO.FS.createDirAll directory
    fixtureDirectory.set (some directory)
    return directory
  return (directory / file).toString

initialize projectionFixtureStore : SimplePersistentEnvExtension KernelProjectionRecord
    (Array KernelProjectionRecord) ← registerSimplePersistentEnvExtension {
  addEntryFn := Array.push
  addImportedFn := fun entries => entries.foldl (· ++ ·) #[] }

end LeanInformationAudit.Tests.Projection
