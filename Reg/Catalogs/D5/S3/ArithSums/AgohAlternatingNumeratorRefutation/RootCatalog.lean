import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ArithSums.AgohAlternatingNumeratorRefutation
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation
import Reg.Support.AgohCoefficientReadoutTemplate

namespace Reg.Catalogs.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.result), theoremName := `D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.result, objectArenaName := `D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.coefficientArena, statementIdentity := some "sha256:b73243ac35b37e86857cc49f737e76604efcfd51d65dcf3d47ee5b444345ba32", registrationModuleName := `Reg.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.result), theoremName := `D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.result, objectArenaName := `D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.coefficientArena, statementIdentity := some "sha256:b73243ac35b37e86857cc49f737e76604efcfd51d65dcf3d47ee5b444345ba32", registrationModuleName := `Reg.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation } }

end Reg.Catalogs.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.RootCatalog
