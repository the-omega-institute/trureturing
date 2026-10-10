import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration
import Reg.Support.MechanicalDyadicRegistration

namespace Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.joint_phase_calibration_law), theoremName := `D5.S1.Words.Mechanical.MechanicalPhaseCalibration.joint_phase_calibration_law, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration.phaseArena, statementIdentity := some "sha256:46ab84fc00f32e087739c4648260bfde5b9e5b16a6b25ed0fa6ee6b92f10a371", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration }],
  source := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.joint_phase_calibration_law), theoremName := `D5.S1.Words.Mechanical.MechanicalPhaseCalibration.joint_phase_calibration_law, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration.phaseArena, statementIdentity := some "sha256:46ab84fc00f32e087739c4648260bfde5b9e5b16a6b25ed0fa6ee6b92f10a371", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration } }

end Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.RootCatalog
