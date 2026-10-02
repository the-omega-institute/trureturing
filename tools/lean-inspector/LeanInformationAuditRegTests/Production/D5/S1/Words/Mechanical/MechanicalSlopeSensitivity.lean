import Reg.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

noncomputable section
namespace Reg.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity
open Set MeasureTheory
open LeanInformationAudit
open _root_.D5.S1.Words.Mechanical
open _root_.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S1.Words.Mechanical.MechanicalSlopeSensitivity.local_slope_disagreement_law
  unless row.any (fun record => match record.result with
      | .declaredValidated _ => true
      | _ => false) do
    throwError "slope-sensitivity information registration is not declaredValidated"

end Reg.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity
