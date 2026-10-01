import LeanInformationAuditRegTests.ContractMapping
import Reg.ContractPrototype.Inline
import Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion

open Lean Meta Elab Command LeanInformationAudit

run_cmd do
  let saved := (← getEnv).setExporting false
  setEnv saved
  liftTermElabM do
    let original := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion
    let prototype := `Reg.ContractPrototype.Inline
    let reports ← ContractPrototype.reports #[original, prototype]
    let some (_, _, oldEnv) := reports[0]? | throwError "missing original report"
    let some (_, _, newEnv) := reports[1]? | throwError "missing prototype report"
    let oldRecord := ((TemplateBinding.records oldEnv).filter
      (·.occurrence.key.registrationModule == original))[0]!
    let newRecord := ((TemplateBinding.records newEnv).filter
      (·.occurrence.key.registrationModule == prototype))[0]!
    discard <| LeanInformationAuditRegTests.ContractMapping.run oldEnv newEnv
      #[(original, prototype),
        (`Reg.Support.BoundedRunSpace, `Reg.ContractPrototype.Templates.Cut)] oldRecord newRecord
    setEnv saved
