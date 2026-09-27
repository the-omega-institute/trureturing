import LeanInformationAudit.Tests.Seal.M3
import LeanInformationAudit.SealCommand

open Lean Lean.Elab.Command LeanInformationAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-! Export the already compiled M3 stage in a separate process.

This file is a temporary measurement companion.  It does not alter M3, repeat
the seal, or participate in the timed samples.  The destination is supplied by
the runner and is the only output owned by the command.
-/

run_cmd do
  let some path ← IO.getEnv "M3_ANALYSIS_PATH"
    | throwError "M3_ANALYSIS_PATH is required"
  let rootId := mkIdent (`_root_ ++ `LeanInformationAudit.Tests.Seal.M3)
  elabCommand (← `(command| #export_information_analysis root $rootId:ident
    analysis_output $(Syntax.mkStrLit path):str))
