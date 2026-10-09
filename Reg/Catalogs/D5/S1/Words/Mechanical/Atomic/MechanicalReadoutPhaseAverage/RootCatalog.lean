import LeanInformationAuditInterface.Contract.Catalog
import D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage
import D5.S3.ConceptDynamics.InformationEscape.MechanicalPhaseAverageRegistration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage
import Reg.Support.PointwiseEqualityRegistrations

namespace Reg.Catalogs.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_phase_average), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_phase_average, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalPhaseAverageRegistration.phaseAverageArena, statementIdentity := some "sha256:c5da0649ff1675503963a41a48ceac32ae9c8be19ab3a7d9baf2a52cbbafecea", registrationModuleName := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage }],
  source := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_phase_average), theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_phase_average, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalPhaseAverageRegistration.phaseAverageArena, statementIdentity := some "sha256:c5da0649ff1675503963a41a48ceac32ae9c8be19ab3a7d9baf2a52cbbafecea", registrationModuleName := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage } }

end Reg.Catalogs.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.RootCatalog
