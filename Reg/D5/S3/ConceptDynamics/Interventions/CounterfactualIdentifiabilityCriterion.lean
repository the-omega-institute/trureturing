import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
import Reg.Support.SharedArenaPeers

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber,
      statementIdentity := "sha256:cb61e898923980980a8546c9854a68fceece05576107f21c3d55ce166b9297aa",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable,
      statementIdentity := "sha256:a8c89fcc1db5d6e828261153109783acdf6c889d18caab542dfa8b17800caf2c",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber,
      statementIdentity := "sha256:cb61e898923980980a8546c9854a68fceece05576107f21c3d55ce166b9297aa",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable,
      statementIdentity := "sha256:a8c89fcc1db5d6e828261153109783acdf6c889d18caab542dfa8b17800caf2c",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion }

namespace Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion

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

register_information_theorem _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber in finiteInterventionLawArena
  object_arena finiteInterventionArena catalog finiteProbe
  readout via (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M))
  primitives finiteInterventionRealization.toPrimitiveBundle realization finiteFiber_bridge
  variation finiteIntervention_law_sensitive sensitivity finiteIntervention_slot_sensitive
  escape from (BooleanCoupling) escape continues (finiteIntervention_empty)
end

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

register_information_theorem _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable in finiteInterventionLawArena
  object_arena finiteInterventionArena catalog finiteProbe
  readout via (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M))
  primitives finiteInterventionRealization.toPrimitiveBundle realization finiteNotIdentifiable_bridge
  variation finiteIntervention_law_sensitive sensitivity finiteIntervention_slot_sensitive
  escape from (DeterministicBoolSCM) escape continues (finiteIntervention_empty)
end

end Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion
