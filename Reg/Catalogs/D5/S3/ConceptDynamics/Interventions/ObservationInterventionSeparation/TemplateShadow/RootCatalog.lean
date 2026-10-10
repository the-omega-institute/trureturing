import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow
import Reg.Support.LegacyCausalMapping

namespace Reg.Catalogs.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention), theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena, statementIdentity := some "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention), theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena, statementIdentity := some "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow } }

end Reg.Catalogs.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow.RootCatalog
