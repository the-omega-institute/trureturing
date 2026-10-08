import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicSeriesRegistration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries
import Reg.Support.MechanicalDyadicRegistration

namespace Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries.geometric_readout_floor_series_and_mass), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries.geometric_readout_floor_series_and_mass, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicSeriesRegistration.seriesArena, statementIdentity := some "sha256:fd1a4e1caf3744647b114425eeaf3607fbbc885af074c2b36fda2f72411e9fd8", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries }],
  source := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries.geometric_readout_floor_series_and_mass), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries.geometric_readout_floor_series_and_mass, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicSeriesRegistration.seriesArena, statementIdentity := some "sha256:fd1a4e1caf3744647b114425eeaf3607fbbc885af074c2b36fda2f72411e9fd8", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries } }

end Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries.RootCatalog
