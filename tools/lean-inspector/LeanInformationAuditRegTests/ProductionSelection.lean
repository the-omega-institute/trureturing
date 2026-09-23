import Reg.Catalogs.InformationRoot
import LeanInformationAuditRegTests.ProductionInputs

open Lean Lean.Elab.Command LeanInformationAudit LeanInformationAuditRegTests

private def rejectsSelection (label : String) (rows : Array SnapshotOccurrence) : CommandElabM Unit := do
  let rejected ← try
    discard <| liftCoreM <| productionEntries rows
    pure false
  catch _ => pure true
  unless rejected do throwError "[FAIL] production selection accepted {label}"
  logInfo m!"[PASS] production_selection_rejects_{label}"

-- Guard the migration seam against vacuous success and against substituting a
-- catalog owner for the independently supplied registration contributor.
run_cmd do
  let rows := Reg.Support.InformationRootContract.contract.expected
  unless rows.size == 11 do throwError "expected eleven independent production rows"
  let actual ← liftCoreM <| productionEntries rows
  unless actual.size == 11 do throwError "expected eleven actual production rows"
  rejectsSelection "empty" #[]
  rejectsSelection "catalog_as_contributor" <| rows.modify 0 fun row =>
    { row with registrationModuleName := Reg.Support.InformationRootContract.rootId }
  rejectsSelection "duplicate_occurrence" (rows.push rows[0]!)
