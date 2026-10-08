import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
import Reg.Support.PointwiseEqualityRegistrations

namespace Reg.Catalogs.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction), theoremName := `D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena, statementIdentity := some "sha256:3cedb82534e585ab1c5cb122ef9b78447ce5288c441f3c5cde230fe1ea477fcc", registrationModuleName := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction), theoremName := `D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena, statementIdentity := some "sha256:3cedb82534e585ab1c5cb122ef9b78447ce5288c441f3c5cde230fe1ea477fcc", registrationModuleName := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates } }

end Reg.Catalogs.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.RootCatalog
