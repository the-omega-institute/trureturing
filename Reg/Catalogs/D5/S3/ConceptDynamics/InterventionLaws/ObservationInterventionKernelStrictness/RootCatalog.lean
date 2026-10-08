import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness
import Reg.Support.SharedArenaPeers

namespace Reg.Catalogs.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation), theoremName := `D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena, statementIdentity := some "sha256:87ec84d0c4c656a0524de84c33660dda95d43fde6d2b8c2284d448a1efbb5391", registrationModuleName := `Reg.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation), theoremName := `D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena, statementIdentity := some "sha256:87ec84d0c4c656a0524de84c33660dda95d43fde6d2b8c2284d448a1efbb5391", registrationModuleName := `Reg.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness } }

end Reg.Catalogs.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.RootCatalog
