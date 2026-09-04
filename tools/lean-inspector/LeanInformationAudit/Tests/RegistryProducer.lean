import LeanInformationAudit.Registry

open Lean
open LeanInformationAudit

run_cmd
  Lean.Elab.Command.liftCoreM do
    modifyEnv fun env =>
      informationRegistryExt.addEntry env {
        theoremName := `LeanInformationAudit.Tests.probeTheorem
        unitName := `LeanInformationAudit.Tests.probeTheorem.__information_unit
        arenaName := `LeanInformationAudit.Tests.probeArena
        realizationName := .anonymous
      }
