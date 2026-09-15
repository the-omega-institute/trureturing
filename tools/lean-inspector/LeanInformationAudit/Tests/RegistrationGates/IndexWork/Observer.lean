import LeanInformationAudit.Tests.RegistrationGates.IndexWork.Selected

namespace LeanInformationAudit.Tests.IndexWork
open Lean Elab Command TemplateAudit

structure Measurement where
  population : Nat
  selective : Bool
  visits : Nat
  retainedBytes : Nat
  planIdentity : String
  nativeInputs : Array String
  deriving Inhabited

initialize measurements : SimplePersistentEnvExtension Measurement (Array Measurement) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }

/-- This counter is driven by the actual lookup's node/edge effects, never by a
claimed work result. Each row is captured in its own compiled import environment. -/
elab "measure_imported_template_query " population:num selective:num : command => do
  let env ← getEnv
  let count := if selective.getNat == 1 then 1 else population.getNat
  for index in [:32] do
    let suffix := "other" ++ (if index < 10 then "0" else "") ++ toString index
    let name := Name.str `DTRIndex.Z suffix
    let present := (selectedPlan env name).isOk
    unless present == (index + 1 < count) do
      throwError "setup: imported enrollment count differs at {suffix}"
  let action : StateM Nat (Except String TemplatePlanData) :=
    observeSelectedPlan env `DTRIndex.A.selected (modify (· + 1))
  let (.ok plan, visits) := action.run 0 | throwError "setup: selected template missing"
  unless plan.name == `DTRIndex.A.selected && plan.slots.size == 2 do
    throwError "setup: selected plan changed"
  liftTermElabM do
    withCumulativeBudget <| NativeCoherence.validate #[plan.definitionOwner, plan.enrollmentOwner]
  let nativeInputs := NativeCoherence.lastInputs (← getEnv)
  let retainedBytes := importedSummaryBytes env
  unless retainedBytes > 0 && retainedBytes ≤ 8388608 do
    throwError "setup: workload is not an admitted imported index"
  modifyEnv fun current => measurements.addEntry current {
    population := population.getNat, selective := selective.getNat == 1,
    visits, retainedBytes, nativeInputs, planIdentity := plan.planIdentity }

elab "check_imported_template_queries" : command => do
  let rows := measurements.getState (← getEnv)
  let selective := rows.filter (·.selective)
  let all := rows.filter (! ·.selective)
  unless selective.map (·.population) == #[1, 9, 33] && all.map (·.population) == #[1, 9, 33] do
    throwError "setup: missing independent workload environment"
  let first := selective[0]!
  let stable := rows.all (·.planIdentity == first.planIdentity)
  let control := stable && selective.all (fun row =>
    row.visits == first.visits && row.retainedBytes == first.retainedBytes)
  let bound := 2 * "DTRIndex.A.selected".utf8ByteSize + 1
  let within := all.all (·.visits ≤ bound)
  let nativeStable := !first.nativeInputs.isEmpty && rows.all (·.nativeInputs == first.nativeInputs)
  let growing := all[0]!.retainedBytes < all[1]!.retainedBytes &&
    all[1]!.retainedBytes < all[2]!.retainedBytes
  unless growing do throwError "setup: All workload did not import a growing index"
  logInfo m!"[{if control then "PASS" else "FAIL"}] selective_n_scaling_control"
  logInfo m!"[{if stable then "PASS" else "FAIL"}] selected_query_result_accepted"
  logInfo m!"[{if within then "PASS" else "FAIL"}] selected_query_work_independent_of_n"
  logInfo m!"[{if nativeStable then "PASS" else "FAIL"}] native_selected_inputs_independent_of_n"
  for row in rows do
    logInfo m!"DTR_QUERY population={row.population} selective={row.selective} visits={row.visits} imported_bytes={row.retainedBytes} native_inputs={row.nativeInputs.size} bound={bound}"

end LeanInformationAudit.Tests.IndexWork
