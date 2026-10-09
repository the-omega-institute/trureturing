import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ArithUnits.CenteredReducedResidueProgressions
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S3.ArithUnits.CenteredReducedResidueProgressions
import Reg.Support.CenteredReducedResidueProgressions

namespace Reg.Catalogs.D5.S3.ArithUnits.CenteredReducedResidueProgressions.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.ArithUnits.CenteredReducedResidueProgressions.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ArithUnits.CenteredReducedResidueProgressions.result), theoremName := `D5.S3.ArithUnits.CenteredReducedResidueProgressions.result, objectArenaName := `D5.S3.ArithUnits.CenteredReducedResidueProgressions.sourceCorrectionArena, statementIdentity := some "sha256:5a77f26ee7365ea9923803e0ce97d28ca3bca757eff91584fac525404d475477", registrationModuleName := `Reg.D5.S3.ArithUnits.CenteredReducedResidueProgressions }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ArithUnits.CenteredReducedResidueProgressions.result), theoremName := `D5.S3.ArithUnits.CenteredReducedResidueProgressions.result, objectArenaName := `D5.S3.ArithUnits.CenteredReducedResidueProgressions.sourceCorrectionArena, statementIdentity := some "sha256:5a77f26ee7365ea9923803e0ce97d28ca3bca757eff91584fac525404d475477", registrationModuleName := `Reg.D5.S3.ArithUnits.CenteredReducedResidueProgressions }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.ArithUnits.CenteredReducedResidueProgressions } }

end Reg.Catalogs.D5.S3.ArithUnits.CenteredReducedResidueProgressions.RootCatalog
