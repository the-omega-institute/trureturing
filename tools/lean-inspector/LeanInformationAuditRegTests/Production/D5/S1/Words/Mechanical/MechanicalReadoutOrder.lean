import Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

noncomputable section
namespace Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder
open Set MeasureTheory
open LeanInformationAudit
open _root_.D5.S1.Words.Mechanical.MechanicalReadoutOrder
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Lean in
run_meta do
  for theoremName in #[
      `D5.S1.Words.Mechanical.MechanicalReadoutOrder.local_order_iff_decreasing_weights,
      `D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometric_readout_isometric_completion] do
    let row := (TemplateBinding.records (← getEnv)).find? fun record =>
      record.occurrence.key.theoremName == theoremName
    let valid := row.any fun record => match record.result with
      | .declaredValidated _ => true
      | _ => false
    unless valid do throwError "mechanical order registration is not declaredValidated: {theoremName}"

end Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder
