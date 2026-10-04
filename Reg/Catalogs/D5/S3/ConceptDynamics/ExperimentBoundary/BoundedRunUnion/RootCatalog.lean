import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion
import Reg.Support.BoundedRunSpace

namespace Reg.Catalogs.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary), theoremName := `D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary, objectArenaName := `D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace.bitArena, statementIdentity := some "sha256:f688347ef95d3a1cf53c6f55feb29b319696b0379f090aaf028b0b756d7a0c03", registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary), theoremName := `D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary, objectArenaName := `D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace.bitArena, statementIdentity := some "sha256:f688347ef95d3a1cf53c6f55feb29b319696b0379f090aaf028b0b756d7a0c03", registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion } }

end Reg.Catalogs.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.RootCatalog
