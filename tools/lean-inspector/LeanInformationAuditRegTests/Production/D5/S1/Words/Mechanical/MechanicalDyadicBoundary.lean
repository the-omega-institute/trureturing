import Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

noncomputable section
namespace Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary
open _root_.D5.S1.Words.Mechanical
open _root_.D5.S1.Words.Mechanical.MechanicalDyadicBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open LeanInformationAudit
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
open Lean in
run_meta do
  for theoremName in #[
      `D5.S1.Words.Mechanical.MechanicalDyadicBoundary.dyadic_upper_eventually_word_eq,
      `D5.S1.Words.Mechanical.MechanicalDyadicBoundary.finite_word_stable_off_integer_hits] do
    let row := (TemplateBinding.records (← getEnv)).find? fun record =>
      record.occurrence.key.theoremName == theoremName
    let valid := row.any fun record => match record.result with
      | .declaredValidated _ => true
      | _ => false
    unless valid do throwError "mechanical dyadic information registration is not declaredValidated: {theoremName}"

end Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary
