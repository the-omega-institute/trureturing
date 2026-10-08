import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling
import Reg.Support.IffRegistrations

namespace Reg.Catalogs.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled), theoremName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, statementIdentity := some "sha256:48183359aa256091e3dfc2a80a5352b99a62f3ff03446236a0e6d9bd82fa988e", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled), theoremName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, statementIdentity := some "sha256:48183359aa256091e3dfc2a80a5352b99a62f3ff03446236a0e6d9bd82fa988e", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling } }

end Reg.Catalogs.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.RootCatalog
