import Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

noncomputable section
namespace Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit
open Set Filter
open scoped Topology
open LeanInformationAudit
open _root_.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Lean in
run_meta do
  for theoremName in #[
      `D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound] do
    let row := (TemplateBinding.records (← getEnv)).find? fun record =>
      record.occurrence.key.theoremName == theoremName
    let valid := row.any fun record => match record.result with
      | .declaredValidated _ => true
      | _ => false
    unless valid do throwError "mechanical limit registration is not declaredValidated: {theoremName}"

end Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit
