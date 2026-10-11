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
import Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.InformationRoot
import Reg.Support.LegacyResidue

namespace Reg.Catalogs.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.InformationRoot.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.InformationRoot.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification), theoremName := `D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification, objectArenaName := `Reg.Support.LegacyResidue.arena, statementIdentity := some "sha256:6f8434c94b05962f830bd9c47522da114d168db8b17fa7825970bf48a600b9e6", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.InformationRoot }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification), theoremName := `D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification, objectArenaName := `Reg.Support.LegacyResidue.arena, statementIdentity := some "sha256:6f8434c94b05962f830bd9c47522da114d168db8b17fa7825970bf48a600b9e6", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.InformationRoot }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.InformationRoot } }

end Reg.Catalogs.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.InformationRoot.RootCatalog
