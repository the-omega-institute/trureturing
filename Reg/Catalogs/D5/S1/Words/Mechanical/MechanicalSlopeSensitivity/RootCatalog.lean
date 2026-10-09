import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity
import Reg.Support.MechanicalDyadicRegistration

namespace Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity.local_slope_disagreement_law), theoremName := `D5.S1.Words.Mechanical.MechanicalSlopeSensitivity.local_slope_disagreement_law, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration.slopeArena, statementIdentity := some "sha256:cd8771064a2ef41ff0a64b8419849ed8b69981f7bf5a40ebfe2d070a43075b25", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity }],
  source := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity.local_slope_disagreement_law), theoremName := `D5.S1.Words.Mechanical.MechanicalSlopeSensitivity.local_slope_disagreement_law, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration.slopeArena, statementIdentity := some "sha256:cd8771064a2ef41ff0a64b8419849ed8b69981f7bf5a40ebfe2d070a43075b25", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity } }

end Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalSlopeSensitivity.RootCatalog
