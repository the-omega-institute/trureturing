import LeanInformationAuditInterface.Contract.Catalog
import D5.S1.Words.Mechanical.MechanicalDyadicBoundary
import D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary
import Reg.Support.MechanicalDyadicRegistration

namespace Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalDyadicBoundary.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalDyadicBoundary.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalDyadicBoundary.dyadic_upper_eventually_word_eq), theoremName := `D5.S1.Words.Mechanical.MechanicalDyadicBoundary.dyadic_upper_eventually_word_eq, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.upperArena, statementIdentity := some "sha256:cd129c14a2561274769568cc1b202f52388daa5a0bade1344c03ab7761260418", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary },
    { statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalDyadicBoundary.finite_word_stable_off_integer_hits), theoremName := `D5.S1.Words.Mechanical.MechanicalDyadicBoundary.finite_word_stable_off_integer_hits, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.stableArena, statementIdentity := some "sha256:a4092d2733c8819e7e7bae60e764686bbcbb4ab064a2adbcf8601fce8ed682ae", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary }],
  source := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalDyadicBoundary.dyadic_upper_eventually_word_eq), theoremName := `D5.S1.Words.Mechanical.MechanicalDyadicBoundary.dyadic_upper_eventually_word_eq, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.upperArena, statementIdentity := some "sha256:cd129c14a2561274769568cc1b202f52388daa5a0bade1344c03ab7761260418", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary },
    { statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalDyadicBoundary.finite_word_stable_off_integer_hits), theoremName := `D5.S1.Words.Mechanical.MechanicalDyadicBoundary.finite_word_stable_off_integer_hits, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.stableArena, statementIdentity := some "sha256:a4092d2733c8819e7e7bae60e764686bbcbb4ab064a2adbcf8601fce8ed682ae", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S1.Words.Mechanical.MechanicalDyadicBoundary } }

end Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalDyadicBoundary.RootCatalog
