import LeanInformationAudit.Syntax
import D5.S3.ArithUnits.CenteredReducedResidueProgressions
import Reg.Support.CenteredReducedResidueProgressions

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ArithUnits.CenteredReducedResidueProgressions
  expected := #[
    { objectArenaName := `D5.S3.ArithUnits.CenteredReducedResidueProgressions.sourceCorrectionArena, theoremName := `D5.S3.ArithUnits.CenteredReducedResidueProgressions.result,
      statementIdentity := "sha256:5a77f26ee7365ea9923803e0ce97d28ca3bca757eff91584fac525404d475477",
      registrationModuleName := `Reg.D5.S3.ArithUnits.CenteredReducedResidueProgressions }]
  source := #[
    { objectArenaName := `D5.S3.ArithUnits.CenteredReducedResidueProgressions.sourceCorrectionArena, theoremName := `D5.S3.ArithUnits.CenteredReducedResidueProgressions.result,
      statementIdentity := "sha256:5a77f26ee7365ea9923803e0ce97d28ca3bca757eff91584fac525404d475477",
      registrationModuleName := `Reg.D5.S3.ArithUnits.CenteredReducedResidueProgressions }]
  companionPrefix := some `Reg.D5.S3.ArithUnits.CenteredReducedResidueProgressions }

namespace Reg.D5.S3.ArithUnits.CenteredReducedResidueProgressions

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ArithUnits.CenteredReducedResidueProgressions
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
open LeanInformationAudit
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _root_.D5.S3.ArithUnits.CenteredReducedResidueProgressions.instDecidableEqStateSourceCorrectionArena in

register_information_theorem _root_.D5.S3.ArithUnits.CenteredReducedResidueProgressions.result in sourceCorrectionArena
  readout via (sourceCorrectionRealization (fun x : Bool => x))
  primitives (actualSourceCorrectionRealization).toPrimitiveBundle
  realization inline (actualSourceCorrectionRealization) := by exact ⟨Iff.rfl⟩
  variation sourceCorrection_variation sensitivity sourceCorrection_sensitivity
  escape from (SourceCorrection) escape continues (open)
end

end Reg.D5.S3.ArithUnits.CenteredReducedResidueProgressions
