import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S0.Tower.DBonacci.Substitution
import Reg.Support.PointwiseEqualityRegistrations

namespace Reg.Catalogs.D5.S0.Tower.DBonacci.Substitution.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S0.Tower.DBonacci.Substitution.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible), theoremName := `D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena, statementIdentity := some "sha256:b30ce4d291640ad8d50484250e17905625944a4356233ef3b10bb285576eb0e0", registrationModuleName := `Reg.D5.S0.Tower.DBonacci.Substitution }],
  source := #[{ statement := (_), proof := (@_root_.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible), theoremName := `D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena, statementIdentity := some "sha256:b30ce4d291640ad8d50484250e17905625944a4356233ef3b10bb285576eb0e0", registrationModuleName := `Reg.D5.S0.Tower.DBonacci.Substitution }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S0.Tower.DBonacci.Substitution } }

end Reg.Catalogs.D5.S0.Tower.DBonacci.Substitution.RootCatalog
