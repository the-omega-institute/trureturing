import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Permutation
import D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction

open Lean Elab Command in
run_cmd do
  for name in (← getEnv).header.moduleNames do
    logInfo m!"IMPORT_MODULE {name}"
