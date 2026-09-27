import LeanInformationAudit.Tests.RegistrationGates.IndexWork.Selected

namespace LeanInformationAudit.TemplateAudit
open Lean Meta

run_meta do
  let env ← getEnv
  let name := `LeanInformationAudit.Tests.RegistrationGates.IndexWork.Selected
  withCumulativeBudget <| NativeCoherence.validate #[name]
  logInfo "[PASS] loaded_native_source_coherence_accepted"
  withCumulativeBudget <| NativeCoherence.validate #[name]
  logInfo "[PASS] loaded_native_snapshot_reuse_accepted"
  setEnv env

end LeanInformationAudit.TemplateAudit
