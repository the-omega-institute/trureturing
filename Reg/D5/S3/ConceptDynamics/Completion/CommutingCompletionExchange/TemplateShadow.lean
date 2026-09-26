import Reg.Support.LegacyRelations.Completion
import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena, theoremName := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary,
      statementIdentity := "sha256:1aed443dafdf76d41d4cca3a5a8bbf76e5a0f33e4a90453061b57fc3f432fb0a",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena, theoremName := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary,
      statementIdentity := "sha256:1aed443dafdf76d41d4cca3a5a8bbf76e5a0f33e4a90453061b57fc3f432fb0a",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow }

namespace Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow

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
open _root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
open InformationEscapeArenas.CommutingCompletionExchange

register_information_theorem _root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary
  in commutingCompletionArena
  readout via (_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize
    Reg.Support.LegacyRelations.Completion.signature Reg.Support.LegacyRelations.Completion.actual.readout Reg.Support.LegacyRelations.Completion.actual.anchor)
  realizes Reg.Support.LegacyRelations.Completion.registration
  finite via completion_bridge
  variation Reg.Support.LegacyRelations.Completion.finite_variation sensitivity Reg.Support.LegacyRelations.Completion.finite_sensitivity
  escape from source (Reg.Support.LegacyRelations.Completion.selection)
  escape continues (open)
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
open _root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
open InformationEscapeArenas.CommutingCompletionExchange
example : _root_.Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary.__information_unit.Statement =
    (InformationEscapeRealizations.CommutingCompletionExchange.commutativity_hypothesis_is_necessary_realization.toTheoremUnit
      commutativity_hypothesis_is_necessary).Statement := rfl
end

end Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow
