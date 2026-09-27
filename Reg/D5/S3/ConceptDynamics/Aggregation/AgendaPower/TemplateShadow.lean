import Reg.Support.LegacyAgenda
import LeanInformationAudit.SealCommand

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow
  expected := #[
    { objectArenaName := `Reg.Support.LegacyAgenda.arena, theoremName := `D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power,
      statementIdentity := "sha256:384a1edc32c16ec0b4045c373ce00d995b3fa571bb9cbf36960355b33a93cc00",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow }]
  source := #[
    { objectArenaName := `Reg.Support.LegacyAgenda.arena, theoremName := `D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power,
      statementIdentity := "sha256:384a1edc32c16ec0b4045c373ce00d995b3fa571bb9cbf36960355b33a93cc00",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow }


namespace Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.Reg.Support.LegacyFiniteTransport
open _root_.Reg.Support.LegacyAgenda

register_information_theorem _root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power in arena
  readout via (agendaRealization (fun s => winnerCode s) (fun s => valid s))
  primitives actual.toPrimitiveBundle
  realization bridge
  variation variation
  sensitivity sensitivity
  escape from (_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.Agenda) escape continues (open)

end Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow
