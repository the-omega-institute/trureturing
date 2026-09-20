import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
import Reg.Support.SharedArenaPeers

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer,
      statementIdentity := "sha256:1a6132946d7a8891764ed2653324de2bf30ed7e60a456bc3718245df3f8e4916",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer,
      statementIdentity := "sha256:1a6132946d7a8891764ed2653324de2bf30ed7e60a456bc3718245df3f8e4916",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner }

namespace Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner

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
open _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
open _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion
open _root_.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative
open _root_.D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization
open _root_.D5.S3.ConceptDynamics.ConceptJoinUniversal
open FourthFifthArenas
attribute [local instance] modelFintype modelDecidableEq in

register_information_theorem _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer in finiteInterventionLawArena
  object_arena finiteInterventionArena catalog finiteProbe
  readout via (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M))
  primitives finiteInterventionRealization.toPrimitiveBundle realization finiteFiner_bridge
  variation finiteIntervention_law_sensitive sensitivity finiteIntervention_slot_sensitive
  escape from (DeterministicBoolSCM) escape continues (finiteIntervention_empty)
end

end Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
