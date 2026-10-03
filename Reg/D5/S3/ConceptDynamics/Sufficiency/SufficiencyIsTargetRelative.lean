import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
import Reg.Support.SharedArenaPeers



namespace Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative

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

noncomputable def _root_.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not.«Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionLawArena (And (@D5.S3.ConceptDynamics.ConceptJoinUniversal.Refines.{0, 0, 0} D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM (@Set.Elem.{0} (Bool → Bool → Nat) (@D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization.TargetImage.{0, 0} D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM (Bool → Bool → Nat) D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventionMarginal)) (Bool → Bool → Nat) (@D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization.canonicalTargetReadout.{0, 0} D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM (Bool → Bool → Nat) D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventionMarginal) D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventionMarginal) (Not (@D5.S3.ConceptDynamics.ConceptJoinUniversal.Refines.{0, 0, 0} D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM (@Set.Elem.{0} (Bool → Bool → Bool → Bool) (@D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization.TargetImage.{0, 0} D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM (Bool → Bool → Bool → Bool) D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.counterfactualJoint)) (Bool → Bool → Nat) (@D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization.canonicalTargetReadout.{0, 0} D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM (Bool → Bool → Bool → Bool) D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.counterfactualJoint) D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventionMarginal))) D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionRealization := D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteTarget_bridge

attribute [local instance] modelFintype modelDecidableEq in

noncomputable def _root_.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not.«Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit : D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.{0, 0} (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionLawArena) := @D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionLawArena (And (@D5.S3.ConceptDynamics.ConceptJoinUniversal.Refines.{0, 0, 0} D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM (@Set.Elem.{0} (Bool → Bool → Nat) (@D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization.TargetImage.{0, 0} D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM (Bool → Bool → Nat) D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventionMarginal)) (Bool → Bool → Nat) (@D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization.canonicalTargetReadout.{0, 0} D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM (Bool → Bool → Nat) D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventionMarginal) D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventionMarginal) (Not (@D5.S3.ConceptDynamics.ConceptJoinUniversal.Refines.{0, 0, 0} D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM (@Set.Elem.{0} (Bool → Bool → Bool → Bool) (@D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization.TargetImage.{0, 0} D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM (Bool → Bool → Bool → Bool) D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.counterfactualJoint)) (Bool → Bool → Nat) (@D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization.canonicalTargetReadout.{0, 0} D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM (Bool → Bool → Bool → Bool) D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.counterfactualJoint) D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventionMarginal))) D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionRealization D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not.«Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__primitive_realization D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not

attribute [local instance] modelFintype modelDecidableEq in

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not) (type_of% (finiteInterventionLawArena)) (type_of% (finiteInterventionArena)) (type_of% (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M))) (type_of% (finiteIntervention_law_sensitive)) (type_of% (finiteIntervention_slot_sensitive)) (type_of% (DeterministicBoolSCM)) (type_of% (finiteIntervention_empty)) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Sufficiency") "SufficiencyIsTargetRelative") "interventional_marginal_sufficient_but_counterfactual_joint_not") "Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Sufficiency") "SufficiencyIsTargetRelative") "interventional_marginal_sufficient_but_counterfactual_joint_not") "Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe") "__primitive_realization"),
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteTarget_bridge,
  generated := false,
  arena := ⟨(finiteInterventionLawArena)⟩,
  objectArena := ⟨(finiteInterventionArena)⟩,
  catalog := `finiteProbe,
  localNames := false,
  realization := .legacy (finiteInterventionLawArena) (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionRealization) (finiteInterventionRealization.toPrimitiveBundle) ⟨(finiteTarget_bridge)⟩,
  readout := some (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M)),
  variation := some ⟨(finiteIntervention_law_sensitive)⟩,
  sensitivity := some ⟨(finiteIntervention_slot_sensitive)⟩,
  escapeFrom := some (DeterministicBoolSCM),
  sourceSelection := none,
  continuation := .evidence ⟨(finiteIntervention_empty)⟩,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency.types, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxRecDepth, value := .nat 100000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end

end Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative
