import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder
import Reg.Support.MechanicalDyadicRegistration

namespace Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalReadoutOrder.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalReadoutOrder.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutOrder.local_order_iff_decreasing_weights), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutOrder.local_order_iff_decreasing_weights, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.localOrderArena, statementIdentity := some "sha256:11aadd35f6b85336828d84b165fbeeaa864ee887c147903bedd58ba8f017e6fd", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder },
    { statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometric_readout_isometric_completion), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometric_readout_isometric_completion, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.isometricArena, statementIdentity := some "sha256:89c5ad6ba8c8a28280ac3325089a6260e8d0a103e4225d75d42ff950c5e54762", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder }],
  source := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutOrder.local_order_iff_decreasing_weights), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutOrder.local_order_iff_decreasing_weights, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.localOrderArena, statementIdentity := some "sha256:11aadd35f6b85336828d84b165fbeeaa864ee887c147903bedd58ba8f017e6fd", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder },
    { statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometric_readout_isometric_completion), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometric_readout_isometric_completion, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.isometricArena, statementIdentity := some "sha256:89c5ad6ba8c8a28280ac3325089a6260e8d0a103e4225d75d42ff950c5e54762", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S1.Words.Mechanical.MechanicalReadoutOrder } }

end Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalReadoutOrder.RootCatalog
