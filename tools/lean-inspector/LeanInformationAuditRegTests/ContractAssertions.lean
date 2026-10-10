import Lean

namespace LeanInformationAuditRegTests.ContractGuards
open Lean Meta Elab Command

def assertTest (label : String) (ok : Bool) : MetaM Unit := do
  if ok then logInfo m!"[PASS] {label}"
  else logError m!"[FAIL] {label}"

end LeanInformationAuditRegTests.ContractGuards
