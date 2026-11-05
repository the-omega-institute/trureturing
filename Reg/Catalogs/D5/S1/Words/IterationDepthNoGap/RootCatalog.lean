import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.IterationDepthNoGapRegistration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S1.Words.IterationDepthNoGap
import Reg.Support.IterationDepthNoGapRegistration

namespace Reg.Catalogs.D5.S1.Words.IterationDepthNoGap.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S1.Words.IterationDepthNoGap.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S1.Words.IterationDepthNoGap.result), theoremName := `D5.S1.Words.IterationDepthNoGap.result, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IterationDepthNoGapRegistration.depthNoGapArena, statementIdentity := none, registrationModuleName := `Reg.D5.S1.Words.IterationDepthNoGap }],
  source := #[{ statement := (_), proof := (@_root_.D5.S1.Words.IterationDepthNoGap.result), theoremName := `D5.S1.Words.IterationDepthNoGap.result, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IterationDepthNoGapRegistration.depthNoGapArena, statementIdentity := none, registrationModuleName := `Reg.D5.S1.Words.IterationDepthNoGap }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S1.Words.IterationDepthNoGap } }

end Reg.Catalogs.D5.S1.Words.IterationDepthNoGap.RootCatalog
