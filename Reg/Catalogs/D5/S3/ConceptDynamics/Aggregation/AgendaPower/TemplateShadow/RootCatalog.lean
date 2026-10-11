import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow
import Reg.Support.LegacyAgenda

namespace Reg.Catalogs.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power), theoremName := `D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power, objectArenaName := `Reg.Support.LegacyAgenda.arena, statementIdentity := some "sha256:384a1edc32c16ec0b4045c373ce00d995b3fa571bb9cbf36960355b33a93cc00", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power), theoremName := `D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power, objectArenaName := `Reg.Support.LegacyAgenda.arena, statementIdentity := some "sha256:384a1edc32c16ec0b4045c373ce00d995b3fa571bb9cbf36960355b33a93cc00", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow } }

end Reg.Catalogs.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.RootCatalog
