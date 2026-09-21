import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena, theoremName := `D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power,
      statementIdentity := "sha256:384a1edc32c16ec0b4045c373ce00d995b3fa571bb9cbf36960355b33a93cc00",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena, theoremName := `D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power,
      statementIdentity := "sha256:384a1edc32c16ec0b4045c373ce00d995b3fa571bb9cbf36960355b33a93cc00",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow }

namespace Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow

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
open _root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower
open _root_.D5.S3.ConceptDynamics.Aggregation.MajorityCycleNotScalarOrder
open FirstThreeArenas
attribute [local instance] agendaFintype
attribute [local instance] _root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.instDecidablePredAgendaValidAgenda in

register_information_theorem _root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power in agendaPowerArena
  primitives agendaRealization.toPrimitiveBundle realization agenda_bridge
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
open _root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower
open _root_.D5.S3.ConceptDynamics.Aggregation.MajorityCycleNotScalarOrder
open FirstThreeArenas
attribute [local instance] agendaFintype
attribute [local instance] _root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.instDecidablePredAgendaValidAgenda
example : _root_.Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power.__information_unit.Statement =
    (FirstThreeRealizations.agenda_power_realization.toTheoremUnit agenda_power).Statement := rfl
end

end Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow
