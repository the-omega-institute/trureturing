import LeanInformationAudit.InspectorProducer
import LeanInformationAudit.Sha256

namespace LeanInformationAudit.Tests.DeclaredExportDriver
open Lean

/-- Run after the independent registration fixtures have been built. The driver
itself imports no content environment, so fresh-load RSS is measured once. -/
unsafe def emitArtifacts : IO Unit := do
  if let some directory ← IO.getEnv "DTR_FIXTURE_OUTPUT" then
    let destination := System.FilePath.mk directory
    IO.FS.createDirAll destination
    let mut args := ["--output", (destination / "declared-export.spool.json").toString,
      "--material-spool", (destination / "declared-export.material-spool").toString]
    for moduleName in #["LeanInformationAudit.Tests.RegistrationGates.DeclaredBindings",
        "LeanInformationAudit.Tests.RegistrationGates.DeclaredStructural"] do
      let path := "tools/lean-inspector/" ++ moduleName.replace "." "/" ++ ".lean"
      let identity := Sha256.hex (← IO.FS.readBinFile path)
      args := args ++ [moduleName, path, "sha256:" ++ identity]
    InspectorProducer.main args


end LeanInformationAudit.Tests.DeclaredExportDriver

unsafe def main : IO Unit :=
  LeanInformationAudit.Tests.DeclaredExportDriver.emitArtifacts
