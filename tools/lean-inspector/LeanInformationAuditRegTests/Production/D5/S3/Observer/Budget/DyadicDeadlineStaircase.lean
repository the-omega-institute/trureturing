import Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase
open _root_.D5.S3.Observer.Budget.DyadicDeadlineStaircase
open _root_.D5.S3.Observer.Budget.DyadicPrefixDelayRange
open _root_.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S3.Observer.Budget.DyadicDeadlineStaircase.exceptional_prefix_timing
  let valid := row.any fun record => match record.result with
    | .declaredValidated _ => true
    | _ => false
  unless valid do
    throwError "exceptional_prefix_timing lacks declared_validated binding"
  logInfo "[PASS] exceptional_prefix_timing declared_validated"

end Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase
