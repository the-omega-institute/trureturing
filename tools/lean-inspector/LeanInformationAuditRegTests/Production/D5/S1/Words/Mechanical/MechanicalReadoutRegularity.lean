import Reg.D5.S1.Words.Mechanical.MechanicalReadoutRegularity
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand

noncomputable section
namespace Reg.D5.S1.Words.Mechanical.MechanicalReadoutRegularity
open Set
open LeanInformationAudit
open _root_.D5.S1.Words.Mechanical.MechanicalReadoutRegularity
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S1.Words.Mechanical.MechanicalReadoutRegularity.geometric_readout_continuity_and_jump
  let valid := row.any fun record => match record.result with
    | .declaredValidated _ => true
    | _ => false
  unless valid do throwError "mechanical regularity registration is not declaredValidated"

end Reg.D5.S1.Words.Mechanical.MechanicalReadoutRegularity
