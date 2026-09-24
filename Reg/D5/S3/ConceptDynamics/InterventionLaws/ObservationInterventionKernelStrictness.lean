import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
import Reg.Support.SharedArenaPeers

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena, theoremName := `D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation,
      statementIdentity := "sha256:87ec84d0c4c656a0524de84c33660dda95d43fde6d2b8c2284d448a1efbb5391",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena, theoremName := `D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation,
      statementIdentity := "sha256:87ec84d0c4c656a0524de84c33660dda95d43fde6d2b8c2284d448a1efbb5391",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness }

namespace Reg.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open SharedArenaFiniteTemplates
open EscapeRecord
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open _root_.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness
open InformationEscapeArenas.ObservationIntervention

register_information_theorem _root_.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation
  in finiteObservationInterventionLawArena
  object_arena finiteObservationInterventionArena catalog finiteProbe
  readout via (@observationFiniteRealization DeterministicBoolSCM
    (fun M => oiObsCode M) (fun M => oiIntCode M))
  primitives finiteObservationRealization.toPrimitiveBundle realization finiteProfile_bridge
  variation finiteObservation_law_sensitive sensitivity finiteObservation_slot_sensitive
  escape from (DeterministicBoolSCM) escape continues (finiteObservationResidual)
end

end Reg.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness
