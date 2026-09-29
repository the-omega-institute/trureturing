import Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand

noncomputable section
namespace Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage
open Set MeasureTheory
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalPhaseAverageRegistration
open D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates
open _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_phase_average
  let valid := row.any fun record => match record.result with
    | .declaredValidated _ => true
    | _ => false
  unless valid do throwError "phase-average information registration is not declaredValidated"

end Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage
