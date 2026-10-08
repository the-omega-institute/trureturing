import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S1.Words.Mechanical.MechanicalReadoutRegularity
import Reg.Support.MechanicalDyadicRegistration

namespace Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalReadoutRegularity.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalReadoutRegularity.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutRegularity.geometric_readout_continuity_and_jump), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutRegularity.geometric_readout_continuity_and_jump, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.regularityArena, statementIdentity := some "sha256:ec5cadfc13b74c2674cf501896fe5df3e646220f47ea03bd784cca87bf988f3e", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutRegularity }],
  source := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutRegularity.geometric_readout_continuity_and_jump), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutRegularity.geometric_readout_continuity_and_jump, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.regularityArena, statementIdentity := some "sha256:ec5cadfc13b74c2674cf501896fe5df3e646220f47ea03bd784cca87bf988f3e", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutRegularity }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S1.Words.Mechanical.MechanicalReadoutRegularity } }

end Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalReadoutRegularity.RootCatalog
