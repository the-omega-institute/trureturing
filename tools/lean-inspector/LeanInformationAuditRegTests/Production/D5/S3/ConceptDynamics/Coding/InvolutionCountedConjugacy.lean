import Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand

open _root_.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
open _root_.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy
open _root_.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy
open Lean in
run_meta do
  for name in [`D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.involution_minimum_one,
      `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.natural_factor_products] do
    let row := (TemplateBinding.records (← getEnv)).find? fun r =>
      r.occurrence.key.theoremName == name
    unless row.any (fun r => match r.result with | .declaredValidated _ => true | _ => false) do
      throwError "{name} registration is not declaredValidated"

end Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy
