import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S1.Words.HughesIterationDepthNoGap
import Reg.Support.HughesIterationDepthNoGapRegistration

namespace Reg.Catalogs.D5.S1.Words.HughesIterationDepthNoGap.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S1.Words.HughesIterationDepthNoGap.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S1.Words.HughesIterationDepthNoGap.result), theoremName := `D5.S1.Words.HughesIterationDepthNoGap.result, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration.depthNoGapArena, statementIdentity := some "sha256:230f0680b60411b8adb201199c15d936e8d5cec2ffbba2159b694747c9dc2f0a", registrationModuleName := `Reg.D5.S1.Words.HughesIterationDepthNoGap }],
  source := #[{ statement := (_), proof := (@_root_.D5.S1.Words.HughesIterationDepthNoGap.result), theoremName := `D5.S1.Words.HughesIterationDepthNoGap.result, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration.depthNoGapArena, statementIdentity := some "sha256:230f0680b60411b8adb201199c15d936e8d5cec2ffbba2159b694747c9dc2f0a", registrationModuleName := `Reg.D5.S1.Words.HughesIterationDepthNoGap }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S1.Words.HughesIterationDepthNoGap } }

end Reg.Catalogs.D5.S1.Words.HughesIterationDepthNoGap.RootCatalog
