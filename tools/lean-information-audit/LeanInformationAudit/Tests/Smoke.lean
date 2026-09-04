import LeanInformationAudit.Registry

open Lean

/-- info: 0 -/
#guard_msgs in
#eval do
  return (InformationRegistry.entries (← getEnv)).size
