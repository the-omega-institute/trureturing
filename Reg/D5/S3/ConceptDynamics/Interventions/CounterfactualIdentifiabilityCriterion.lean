import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
import Reg.Support.SharedArenaPeers



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

theorem _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber.«Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionLawArena (@Exists.{1} (Bool → D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanMarginal) fun (μ : Bool → D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanMarginal) => @Exists.{1} D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanCoupling fun (M : D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanCoupling) => @Exists.{1} D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanCoupling fun (N : D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanCoupling) => And (@Membership.mem.{0, 0} D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanCoupling (Set.{0} D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanCoupling) (@Set.instMembership.{0} D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanCoupling) (@D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.couplingFiber.{0, 0} D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanCoupling (Bool → D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanMarginal) D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.allSingleWorldMarginals μ) M) (And (@Membership.mem.{0, 0} D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanCoupling (Set.{0} D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanCoupling) (@Set.instMembership.{0} D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanCoupling) (@D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.couplingFiber.{0, 0} D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanCoupling (Bool → D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanMarginal) D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.allSingleWorldMarginals μ) N) (@Ne.{1} (Bool → Bool → Bool → Bool) (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.CF M) (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.CF N)))) D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionRealization := D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteFiber_bridge



attribute [local instance] modelFintype modelDecidableEq in

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber) (type_of% (finiteInterventionLawArena)) (type_of% (finiteInterventionArena)) (type_of% (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M))) (type_of% (finiteIntervention_law_sensitive)) (type_of% (finiteIntervention_slot_sensitive)) (type_of% (BooleanCoupling)) (type_of% (finiteIntervention_empty)) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "CounterfactualIdentifiabilityCriterion") "boolean_counterfactual_varies_on_coupling_fiber") "Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "CounterfactualIdentifiabilityCriterion") "boolean_counterfactual_varies_on_coupling_fiber") "Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe") "__primitive_realization"),
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteFiber_bridge,
  generated := false,
  arena := ⟨(finiteInterventionLawArena)⟩,
  objectArena := ⟨(finiteInterventionArena)⟩,
  catalog := `finiteProbe,
  localNames := false,
  realization := .legacy (finiteInterventionLawArena) (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionRealization) (finiteInterventionRealization.toPrimitiveBundle) ⟨(finiteFiber_bridge)⟩,
  readout := some (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M)),
  variation := some ⟨(finiteIntervention_law_sensitive)⟩,
  sensitivity := some ⟨(finiteIntervention_slot_sensitive)⟩,
  escapeFrom := some (BooleanCoupling),
  sourceSelection := none,
  continuation := .evidence ⟨(finiteIntervention_empty)⟩,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency.types, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxRecDepth, value := .nat 100000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

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

theorem _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable.«Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionLawArena (Not (@Exists.{1} ((Bool → D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanMarginal) → Bool → Bool → Bool → Bool) fun (f : (Bool → D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanMarginal) → Bool → Bool → Bool → Bool) => @Eq.{1} ((M : D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) → Bool → Bool → Bool → Bool) D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.CF (@Function.comp.{1, 1, 1} D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanCoupling (Bool → D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.BooleanMarginal) (Bool → Bool → Bool → Bool) f D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.allSingleWorldMarginals))) D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionRealization := D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteNotIdentifiable_bridge



attribute [local instance] modelFintype modelDecidableEq in

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable) (type_of% (finiteInterventionLawArena)) (type_of% (finiteInterventionArena)) (type_of% (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M))) (type_of% (finiteIntervention_law_sensitive)) (type_of% (finiteIntervention_slot_sensitive)) (type_of% (DeterministicBoolSCM)) (type_of% (finiteIntervention_empty)) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "CounterfactualIdentifiabilityCriterion") "boolean_counterfactual_not_identifiable") "Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interventions") "CounterfactualIdentifiabilityCriterion") "boolean_counterfactual_not_identifiable") "Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe") "__primitive_realization"),
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteNotIdentifiable_bridge,
  generated := false,
  arena := ⟨(finiteInterventionLawArena)⟩,
  objectArena := ⟨(finiteInterventionArena)⟩,
  catalog := `finiteProbe,
  localNames := false,
  realization := .legacy (finiteInterventionLawArena) (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionRealization) (finiteInterventionRealization.toPrimitiveBundle) ⟨(finiteNotIdentifiable_bridge)⟩,
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

end Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion
