import D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction

open Lean Elab Command in
run_cmd do
  for name in (← getEnv).header.moduleNames do
    logInfo m!"IMPORT_MODULE {name}"
