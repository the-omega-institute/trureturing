import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.SystemUnit
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
import D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
import D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention
import D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit
import Reg.Support.LegacyRelations.System

namespace Reg.Catalogs.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application), theoremName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena, statementIdentity := some "sha256:a3a2c21de13a5366dbb0d8ab39bc747e95b22c7cbeecb7ef39d86092b4c70ab0", registrationModuleName := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application), theoremName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena, statementIdentity := some "sha256:a3a2c21de13a5366dbb0d8ab39bc747e95b22c7cbeecb7ef39d86092b4c70ab0", registrationModuleName := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit } }

end Reg.Catalogs.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.RootCatalog
