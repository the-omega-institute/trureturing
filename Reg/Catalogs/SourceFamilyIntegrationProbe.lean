import Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation

noncomputable section
namespace Reg.Catalogs.SourceFamilyIntegrationProbe
open _root_.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
open _root_.D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape
open LeanInformationAudit
universe u v

-- A disposable occurrence with the same law and the original compiled proofs.
def probeArena : DependentFamily.Arena where
  signature := signature.{u,v}
  Law := arena.{u,v}.Law

def probeRegistration : Registration probeArena.{u,v} (FullLaw identityFamily.{u,v}) where
  actual := actual
  bridge := Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration.bridge
  variation := Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration.variation
  sensitivity := Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration.sensitivity
  dependence := Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration.dependence

register_information_theorem history_law_conditional_expectation in probeArena
  readout via (realize signature.{u,v} (fun _ _ w => w.2) (fun e => nomatch e))
  realizes probeRegistration
  escape from source ({
    owner := `D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
    coordinates := #[0, 0, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "fn", "arg",
        "body", "body", "body", "fn", "arg", "arg", "body", "arg", "arg"]
      stateBinder := 16 }] })
  escape continues (open)


end Reg.Catalogs.SourceFamilyIntegrationProbe
