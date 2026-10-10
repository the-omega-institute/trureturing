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
import Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.InformationRoot
import Reg.Support.LegacyStaticDesign

namespace Reg.Catalogs.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.InformationRoot.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.InformationRoot.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design), theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design, objectArenaName := `Reg.Support.LegacyStaticDesign.arena, statementIdentity := some "sha256:408742a2c71557575944155350def43ed8f9f37ec3a19fe75f721e084dfe939a", registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.InformationRoot }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design), theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design, objectArenaName := `Reg.Support.LegacyStaticDesign.arena, statementIdentity := some "sha256:408742a2c71557575944155350def43ed8f9f37ec3a19fe75f721e084dfe939a", registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.InformationRoot }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.InformationRoot } }

end Reg.Catalogs.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.InformationRoot.RootCatalog
