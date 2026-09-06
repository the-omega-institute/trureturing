import LeanInformationAudit.Tests.Projection.V3Seal
import LeanInformationAudit.OutputOnlyAudit

open Lean Lean.Elab.Command LeanInformationAudit

/-- info: seal publication has no artifact input -/
#guard_msgs in
run_cmd do
  let env ← getEnv
  let some entry := env.constants.toList.find? fun (name, _) =>
      (privateToUserName name).toString == "LeanInformationAudit.elabSealInformationTheory"
    | throwError "missing real seal elaborator"
  match auditSealOutputOnly env entry.1 env.header.mainModule with
  | .ok () => pure ()
  | .error message => throwError message
  unless env.contains `LeanInformationAudit.Tests.Projection.V3Seal.__system_catalog_irredundant do
    throwError "seal publication missing"
  logInfo "seal publication has no artifact input"
