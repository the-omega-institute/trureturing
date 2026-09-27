import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena, theoremName := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause,
      statementIdentity := "sha256:b93e6bd918cabb38e32a21f11542a80c47dcc6ba73bdeac72336a5c75648c24c",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena, theoremName := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause,
      statementIdentity := "sha256:b93e6bd918cabb38e32a21f11542a80c47dcc6ba73bdeac72336a5c75648c24c",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow }

namespace Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations
open _root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
open InformationEscapeArenas.EndStateOmitsPreemptingCause

register_information_theorem _root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause in endStateOmitsPreemptingCauseArena
  primitives preemptionRealization.toPrimitiveBundle realization preemption_bridge
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations
open _root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
open InformationEscapeArenas.EndStateOmitsPreemptingCause
example : _root_.Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause.__information_unit.Statement =
    (InformationEscapeRealizations.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_realization.toTheoremUnit
      end_state_omits_preempting_cause).Statement := rfl
end

end Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow
