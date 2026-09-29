import Reg.Support.DependentFamily
import Reg.Support.FiniteHistoryFamily

noncomputable section
namespace Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
open _root_.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
open _root_.D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u v

/-- The statement parameter is checked against the imported ConstantInfo.type.
The bridge is definitional on the complete thirteen-binder law. -/
def registration : Registration arena.{u,v} (FullLaw identityFamily) where
  actual := actual
  bridge := Iff.rfl
  variation := Reg.Support.FiniteHistoryFamily.variation
  sensitivity := Reg.Support.FiniteHistoryFamily.sensitivity
  dependence := Reg.Support.FiniteHistoryFamily.dependence

register_information_theorem history_law_conditional_expectation in arena
  readout via (realize signature.{u,v} (fun _ _ w => w.2) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
    coordinates := #[0, 1, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "fn", "arg",
        "body", "body", "body", "fn", "arg", "arg", "body", "arg", "arg"]
      stateBinder := 16 }] })
  escape continues (open)

end Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
