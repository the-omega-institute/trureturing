import LeanInformationAudit.Registry

namespace LeanInformationAudit.Tests
open Lean

/-- Source-mutation fixtures use private bytes while the loaded native artifacts
remain read-only at their original absolute search paths. Other compiler processes
continue to see the repository's unchanged sources. -/
def withPrivateSources [Monad m] [MonadEnv m] [MonadFinally m] [MonadLiftT IO m]
    (action : m α) : m α := do
  let original ← IO.Process.getCurrentDir
  let env ← getEnv
  let mut paths := TemplateAudit.policyPaths
  for name in env.header.moduleNames.push env.header.mainModule do
    if name.toString.startsWith "D5." || name.toString.startsWith "LeanInformationAudit." ||
        name == `Trureturing then
      let path := TemplateAudit.sourcePath name
      unless paths.contains path do paths := paths.push path
  IO.FS.withTempDir fun directory => do
    for path in paths do
      let target := directory / path
      if let some parent := target.parent then IO.FS.createDirAll parent
      IO.FS.writeBinFile target (← IO.FS.readBinFile (original / path))
    try
      IO.Process.setCurrentDir directory
      action
    finally
      IO.Process.setCurrentDir original

end LeanInformationAudit.Tests
