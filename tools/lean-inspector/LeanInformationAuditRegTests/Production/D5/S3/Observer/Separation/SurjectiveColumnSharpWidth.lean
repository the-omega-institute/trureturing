import Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

namespace Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth
noncomputable section
open _root_.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.result
  let valid := row.any fun record => match record.result with
    | .declaredValidated _ => true
    | _ => false
  unless valid do throwError "surjective-column registration is not declaredValidated"

end
end Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth
