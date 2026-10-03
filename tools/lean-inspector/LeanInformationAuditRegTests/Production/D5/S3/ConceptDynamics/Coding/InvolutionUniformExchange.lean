import Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open _root_.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
open Lean in
run_meta do
  for name in [`D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.source_ne_target,
      `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.factors_forward,
      `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.factors_reverse] do
    let row := (TemplateBinding.records (← getEnv)).find? fun r =>
      r.occurrence.key.theoremName == name
    unless row.any (fun r => match r.result with | .declaredValidated _ => true | _ => false) do
      throwError "{name} registration is not declaredValidated"

end Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
