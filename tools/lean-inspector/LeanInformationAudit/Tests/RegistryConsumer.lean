import LeanInformationAudit.Tests.RegistryProducer

open Lean
open LeanInformationAudit

/-- info: 1 [LeanInformationAudit.Tests.probeTheorem] -/
#guard_msgs in
run_cmd do
  let es := InformationRegistry.entries (← getEnv)
  logInfo m!"{es.size} {es.map (·.theoremName)}"

#guard_msgs in
run_cmd do
  let env ← getEnv
  unless InformationRegistry.hasTheorem env
      `LeanInformationAudit.Tests.probeTheorem do
    throwError "missing producer theorem name"

#guard_msgs in
run_cmd do
  let env ← getEnv
  unless InformationRegistry.hasUnit env
      `LeanInformationAudit.Tests.probeTheorem.__information_unit do
    throwError "missing producer unit name"

#guard_msgs in
run_cmd do
  let env ← getEnv
  if InformationRegistry.hasTheorem env
      `LeanInformationAudit.Tests.freshTheorem then
    throwError "fresh theorem name unexpectedly present"

#guard_msgs in
run_cmd do
  let env ← getEnv
  let some entry := InformationRegistry.find? env
      `LeanInformationAudit.Tests.probeTheorem
    | throwError "missing imported singleton"
  match ← Lean.Elab.Command.liftTermElabM <| validatePersistedEntry env entry with
  | .ok () => pure ()
  | .error message => throwError message
