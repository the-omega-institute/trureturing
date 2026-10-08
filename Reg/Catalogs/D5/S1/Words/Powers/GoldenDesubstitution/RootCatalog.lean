import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S1.Words.Powers.GoldenDesubstitution
import Reg.Support.PointwiseOrderRegistrations

namespace Reg.Catalogs.D5.S1.Words.Powers.GoldenDesubstitution.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S1.Words.Powers.GoldenDesubstitution.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Powers.substLength_pos), theoremName := `D5.S1.Words.Powers.substLength_pos, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, statementIdentity := some "sha256:c7c23089a7484f261005f23167c5b1588d1b6c64d15914dbdc36e4fe672715db", registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution },
    { statement := (_), proof := (@_root_.D5.S1.Words.Powers.substLength_le_two), theoremName := `D5.S1.Words.Powers.substLength_le_two, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, statementIdentity := some "sha256:17684442190c21bc68cd745b6c7fb89435f2c2c21f60801dbbb02dbc9e3b6eec", registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution }],
  source := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Powers.substLength_pos), theoremName := `D5.S1.Words.Powers.substLength_pos, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, statementIdentity := some "sha256:c7c23089a7484f261005f23167c5b1588d1b6c64d15914dbdc36e4fe672715db", registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution },
    { statement := (_), proof := (@_root_.D5.S1.Words.Powers.substLength_le_two), theoremName := `D5.S1.Words.Powers.substLength_le_two, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, statementIdentity := some "sha256:17684442190c21bc68cd745b6c7fb89435f2c2c21f60801dbbb02dbc9e3b6eec", registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S1.Words.Powers.GoldenDesubstitution } }

end Reg.Catalogs.D5.S1.Words.Powers.GoldenDesubstitution.RootCatalog
