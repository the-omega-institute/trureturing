import OmegaChecks.InitPort.HostedProjection

open Lean

def main (args : List String) : IO Unit := do
  let source :: output :: owners := args | throw <| IO.userError "expected a strict library, output directory and module names"
  OmegaChecks.HostedProjection.write source output (owners.toArray.map String.toName)
