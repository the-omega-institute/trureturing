import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape
import Reg.Support.ExistentialWitnessRegistrationTemplates

namespace Reg.Catalogs.D5.S0.Diagonal.Lawvere.QualitativeEscape.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S0.Diagonal.Lawvere.QualitativeEscape.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint), theoremName := `D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena, statementIdentity := some "sha256:6229f4053788af2b620d04f5df8b8ead8963f1ffb30952697ec73dca847c6886", registrationModuleName := `Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape }],
  source := #[{ statement := (_), proof := (@_root_.D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint), theoremName := `D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena, statementIdentity := some "sha256:6229f4053788af2b620d04f5df8b8ead8963f1ffb30952697ec73dca847c6886", registrationModuleName := `Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape } }

end Reg.Catalogs.D5.S0.Diagonal.Lawvere.QualitativeEscape.RootCatalog
