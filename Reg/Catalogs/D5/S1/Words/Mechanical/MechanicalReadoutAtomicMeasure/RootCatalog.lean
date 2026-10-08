import LeanInformationAuditInterface.Contract.Catalog
import D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
import D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
import Reg.Support.MechanicalDyadicRegistration
import Reg.Support.PointwiseEqualityRegistrations

namespace Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.distributionArena, statementIdentity := some "sha256:e86fbc9eb0eaf8616805c1ac35ac784e9bc227197d2020c6eb701448fc79cf84", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure },
    { statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.hitArena, statementIdentity := some "sha256:d87425086d24ff5a43a67d2dfda1cbd186660c10682806030831e672a496b283", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure },
    { statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_support), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_support, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.supportArena, statementIdentity := some "sha256:578195477c952f318d98ac2002403e3f637cf1444a98e508a938820465abb21a", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure },
    { statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_rational_left_jump_closed_form), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_rational_left_jump_closed_form, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.rationalJumpArena, statementIdentity := some "sha256:f0bf059491cefbf0ae23bfd82a712d76dc87b380a5f51575eff9fc07955fad01", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure }],
  source := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.distributionArena, statementIdentity := some "sha256:e86fbc9eb0eaf8616805c1ac35ac784e9bc227197d2020c6eb701448fc79cf84", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure },
    { statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.hitArena, statementIdentity := some "sha256:d87425086d24ff5a43a67d2dfda1cbd186660c10682806030831e672a496b283", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure },
    { statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_support), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_support, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.supportArena, statementIdentity := some "sha256:578195477c952f318d98ac2002403e3f637cf1444a98e508a938820465abb21a", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure },
    { statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_rational_left_jump_closed_form), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_rational_left_jump_closed_form, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.rationalJumpArena, statementIdentity := some "sha256:f0bf059491cefbf0ae23bfd82a712d76dc87b380a5f51575eff9fc07955fad01", registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure } }

end Reg.Catalogs.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.RootCatalog
