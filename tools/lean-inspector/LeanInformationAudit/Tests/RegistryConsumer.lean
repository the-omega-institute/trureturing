import LeanInformationAudit.Tests.RegistryProducer

open Lean

/-- info: 1 [LeanInformationAudit.Tests.probeTheorem] -/
#guard_msgs in
run_cmd do
  let es := InformationRegistry.entries (← getEnv)
  logInfo m!"{es.size} {es.map (·.theoremName)}"

#guard_msgs in
run_cmd do
  let env ← getEnv
  unless InformationRegistry.containsTheoremName env
      `LeanInformationAudit.Tests.probeTheorem do
    throwError "missing producer theorem name"

#guard_msgs in
run_cmd do
  let env ← getEnv
  unless InformationRegistry.containsUnitName env
      `LeanInformationAudit.Tests.probeTheorem.__information_unit do
    throwError "missing producer unit name"

#guard_msgs in
run_cmd do
  let env ← getEnv
  if InformationRegistry.containsTheoremName env
      `LeanInformationAudit.Tests.freshTheorem then
    throwError "fresh theorem name unexpectedly present"
