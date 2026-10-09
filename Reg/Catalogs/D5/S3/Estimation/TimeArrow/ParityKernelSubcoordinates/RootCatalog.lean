import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
import Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
import Reg.Support.ParityKernelRegistrationTemplates

namespace Reg.Catalogs.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.subcoordinateLaw_eq), theoremName := `D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.subcoordinateLaw_eq, objectArenaName := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.lawArena, statementIdentity := some "sha256:7c157665ce037dde96ecbbb8d69e0cf53810af5a7416ca1930a9ff88e929a20a", registrationModuleName := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.subcoordinateLaw_eq), theoremName := `D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.subcoordinateLaw_eq, objectArenaName := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.lawArena, statementIdentity := some "sha256:7c157665ce037dde96ecbbb8d69e0cf53810af5a7416ca1930a9ff88e929a20a", registrationModuleName := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates } }

end Reg.Catalogs.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.RootCatalog
