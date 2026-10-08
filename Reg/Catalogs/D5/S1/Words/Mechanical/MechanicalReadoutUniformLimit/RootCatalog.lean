import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit
import Reg.Support.MechanicalDyadicRegistration

namespace Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.uniformBoundArena, statementIdentity := some "sha256:ae5c03ecae8ce575308eb4072fd637ff78f2917f57de945667c4772a48a00d3d", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit }],
  source := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.uniformBoundArena, statementIdentity := some "sha256:ae5c03ecae8ce575308eb4072fd637ff78f2917f57de945667c4772a48a00d3d", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit } }

end Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.RootCatalog
