import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.Arith.WuPyramidalComplement
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S3.Arith.WuPyramidalComplement
import Reg.Support.WuPyramidalComplement

namespace Reg.Catalogs.D5.S3.Arith.WuPyramidalComplement.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.Arith.WuPyramidalComplement.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one), theoremName := `D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one, objectArenaName := `D5.S3.Arith.WuPyramidalComplement.branchArena, statementIdentity := some "sha256:417e7452d5a85d1948edbffa69e9940cb47e8a6fb7c15c206b9fa65767ade842", registrationModuleName := `Reg.D5.S3.Arith.WuPyramidalComplement }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one), theoremName := `D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one, objectArenaName := `D5.S3.Arith.WuPyramidalComplement.branchArena, statementIdentity := some "sha256:417e7452d5a85d1948edbffa69e9940cb47e8a6fb7c15c206b9fa65767ade842", registrationModuleName := `Reg.D5.S3.Arith.WuPyramidalComplement }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.Arith.WuPyramidalComplement } }

end Reg.Catalogs.D5.S3.Arith.WuPyramidalComplement.RootCatalog
