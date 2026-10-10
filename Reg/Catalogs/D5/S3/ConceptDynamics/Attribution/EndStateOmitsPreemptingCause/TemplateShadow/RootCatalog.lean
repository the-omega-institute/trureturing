import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow
import Reg.Support.LegacyRelations.Preemption

namespace Reg.Catalogs.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause), theoremName := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena, statementIdentity := some "sha256:b93e6bd918cabb38e32a21f11542a80c47dcc6ba73bdeac72336a5c75648c24c", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause), theoremName := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena, statementIdentity := some "sha256:b93e6bd918cabb38e32a21f11542a80c47dcc6ba73bdeac72336a5c75648c24c", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow } }

end Reg.Catalogs.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow.RootCatalog
