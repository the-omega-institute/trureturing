import Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

noncomputable section
namespace Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
open Set MeasureTheory
open LeanInformationAudit
open _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration
open D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open scoped Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
open Lean in
run_meta do
  for theoremName in #[
      `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic,
      `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit,
      `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_support,
      `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_rational_left_jump_closed_form] do
    let row := (TemplateBinding.records (← getEnv)).find? fun record =>
      record.occurrence.key.theoremName == theoremName
    let valid := row.any fun record => match record.result with
      | .declaredValidated _ => true
      | _ => false
    unless valid do throwError "atomic-measure information registration is not declaredValidated: {theoremName}"

end Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
