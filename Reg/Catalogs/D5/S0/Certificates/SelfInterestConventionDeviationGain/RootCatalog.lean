import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain
import Reg.Support.IffRegistrations

namespace Reg.Catalogs.D5.S0.Certificates.SelfInterestConventionDeviationGain.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S0.Certificates.SelfInterestConventionDeviationGain.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff), theoremName := `D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena, statementIdentity := some "sha256:76175c4656a4be731bad802d770e51ed7e427531bf5c0a2577c86dd338299e1f", registrationModuleName := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain }],
  source := #[{ statement := (_), proof := (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff), theoremName := `D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena, statementIdentity := some "sha256:76175c4656a4be731bad802d770e51ed7e427531bf5c0a2577c86dd338299e1f", registrationModuleName := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain } }

end Reg.Catalogs.D5.S0.Certificates.SelfInterestConventionDeviationGain.RootCatalog
