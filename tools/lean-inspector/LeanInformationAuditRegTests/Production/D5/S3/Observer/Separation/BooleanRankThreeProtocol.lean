import Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
namespace Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol
open _root_.D5.S3.Observer.Separation.BooleanRankThreeProtocol
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S3.Observer.Separation.BooleanRankThreeProtocol.result
  let valid := row.any fun record => match record.result with
    | .declaredValidated _ => true
    | _ => false
  unless valid do throwError "Boolean rank-three protocol registration is not declaredValidated"

end Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol
