import D5.S3.ConceptDynamics.Aggregation.AgendaPower
import D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.CIRPT.PrimitiveKernel
import D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
import D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
import D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
import D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign
import D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
import D5.S3.ConceptDynamics.InformationEscape.SystemUnit
import D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange
import D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
import D5.S3.ConceptDynamics.InformationEscapeCounting.Fused
import D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
import D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
import D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
import D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Reg.Support.LegacyAgenda
import Reg.Support.LegacyCausalCoordinates
import Reg.Support.LegacyCausalFinite
import Reg.Support.LegacyCausalSlots
import Reg.Support.LegacyContextReplacement
import Reg.Support.LegacyFiniteTransport
import Reg.Support.LegacyGluing
import Reg.Support.LegacyResidue
import Reg.Support.LegacySpectrum
import Reg.Support.LegacyStaticDesign
import Mathlib.Tactic.FinCases
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.InformationRoot
import Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot
import Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.InformationRoot
import Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.InformationRoot
import Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.InformationRoot
import Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.InformationRoot
import Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.InformationRoot
import Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit
import Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot
import Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.InformationRoot
import Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot

namespace Reg.Catalogs.InformationRoot.SealedCatalog
open LeanInformationAudit

noncomputable def catalog_0 : Contract.SealCatalog := {
      arenaName := `Reg.Support.LegacyAgenda.arena
      catalogId := `Reg.Support.LegacyAgenda.arena
      arena := (_root_.Reg.Support.LegacyAgenda.arena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateDecidableEq (Reg.Support.LegacyAgenda.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 27
      stateCardEq := by decide +kernel
      full := 132
      fullEq := by letI := ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateFintype; letI := ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.Reg.Support.LegacyAgenda.arena).toArena := _root_.Reg.Support.LegacyAgenda.enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateDecidableEq (Reg.Support.LegacyAgenda.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power) }]; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1; exact (catalog.fusedFull_eq_escapeNumerator states indices).symm.trans (by decide +kernel)
      rows := Fin.cases ({ unique := 570, uniqueEq := by letI := ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateFintype; letI := ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.Reg.Support.LegacyAgenda.arena).toArena := _root_.Reg.Support.LegacyAgenda.enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateDecidableEq (Reg.Support.LegacyAgenda.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power) }]; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1; exact (catalog.fusedUnique_eq_uniqueCaptureCount states indices (0 : Fin 1)).symm.trans (by decide +kernel), without := 702, withoutEq := by letI := ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateFintype; letI := ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.Reg.Support.LegacyAgenda.arena).toArena := _root_.Reg.Support.LegacyAgenda.enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateDecidableEq (Reg.Support.LegacyAgenda.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power) }]; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1; exact (catalog.fusedWithout_eq_escapeNumerator_without states indices (0 : Fin 1)).symm.trans (by decide +kernel), roleBins := ![0, 84, 0, 0, 0, 0, 0, 318, 0, 168, 0, 0, 0, 0, 0], roleEq := by letI := ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateFintype; letI := ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.Reg.Support.LegacyAgenda.arena).toArena := _root_.Reg.Support.LegacyAgenda.enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateDecidableEq (Reg.Support.LegacyAgenda.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power) }]; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1; exact fun bucket => (catalog.fusedRoleBins_eq_roleHistogram states indices (0 : Fin 1) bucket).symm.trans (congrFun (by decide +kernel : (catalog.fusedCounts states indices).roleBins (0 : Fin 1) = ![0, 84, 0, 0, 0, 0, 0, 318, 0, 168, 0, 0, 0, 0, 0]) bucket), roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateDecidableEq (Reg.Support.LegacyAgenda.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateDecidableEq (Reg.Support.LegacyAgenda.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := _root_.Reg.Support.LegacyAgenda.enumeration
    }

noncomputable def facts_0 : Contract.SealFacts catalog_0 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyAgenda.bridge.toTheoremUnit D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_1 : Contract.SealCatalog := {
      arenaName := `Reg.Support.LegacyCausalCoordinates.icObjectArena
      catalogId := `Reg.Support.LegacyCausalCoordinates.icObjectArena
      arena := (_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena)
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.localActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 16
      stateCardEq := by decide +kernel
      full := 0
      fullEq := by let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena) := ⟨([false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c => [false, true].map fun d => (a, b, c, d) : List (Bool × Bool × Bool × Bool)), (by change ([false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c => [false, true].map fun d => (a, b, c, d) : List (Bool × Bool × Bool × Bool)).Nodup; decide +kernel), (by change ([false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c => [false, true].map fun d => (a, b, c, d) : List (Bool × Bool × Bool × Bool)).toFinset = (Finset.univ : Finset (Bool × Bool × Bool × Bool)); decide +kernel)⟩; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.localActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) }]; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1; exact (catalog.fusedFull_eq_escapeNumerator states indices).symm.trans (by decide +kernel)
      rows := Fin.cases ({ unique := 240, uniqueEq := by let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena) := ⟨([false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c => [false, true].map fun d => (a, b, c, d) : List (Bool × Bool × Bool × Bool)), (by change ([false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c => [false, true].map fun d => (a, b, c, d) : List (Bool × Bool × Bool × Bool)).Nodup; decide +kernel), (by change ([false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c => [false, true].map fun d => (a, b, c, d) : List (Bool × Bool × Bool × Bool)).toFinset = (Finset.univ : Finset (Bool × Bool × Bool × Bool)); decide +kernel)⟩; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.localActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) }]; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1; exact (catalog.fusedUnique_eq_uniqueCaptureCount states indices (0 : Fin 1)).symm.trans (by decide +kernel), without := 240, withoutEq := by let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena) := ⟨([false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c => [false, true].map fun d => (a, b, c, d) : List (Bool × Bool × Bool × Bool)), (by change ([false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c => [false, true].map fun d => (a, b, c, d) : List (Bool × Bool × Bool × Bool)).Nodup; decide +kernel), (by change ([false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c => [false, true].map fun d => (a, b, c, d) : List (Bool × Bool × Bool × Bool)).toFinset = (Finset.univ : Finset (Bool × Bool × Bool × Bool)); decide +kernel)⟩; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.localActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) }]; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1; exact (catalog.fusedWithout_eq_escapeNumerator_without states indices (0 : Fin 1)).symm.trans (by decide +kernel), roleBins := ![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], roleEq := by let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena) := ⟨([false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c => [false, true].map fun d => (a, b, c, d) : List (Bool × Bool × Bool × Bool)), (by change ([false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c => [false, true].map fun d => (a, b, c, d) : List (Bool × Bool × Bool × Bool)).Nodup; decide +kernel), (by change ([false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c => [false, true].map fun d => (a, b, c, d) : List (Bool × Bool × Bool × Bool)).toFinset = (Finset.univ : Finset (Bool × Bool × Bool × Bool)); decide +kernel)⟩; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.localActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) }]; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1; exact fun bucket => (catalog.fusedRoleBins_eq_roleHistogram states indices (0 : Fin 1) bucket).symm.trans (congrFun (by decide +kernel : (catalog.fusedCounts states indices).roleBins (0 : Fin 1) = ![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0]) bucket), roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.localActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.localActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := ⟨([false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c => [false, true].map fun d => (a, b, c, d) : List (Bool × Bool × Bool × Bool)), (by change ([false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c => [false, true].map fun d => (a, b, c, d) : List (Bool × Bool × Bool × Bool)).Nodup; decide +kernel), (by change ([false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c => [false, true].map fun d => (a, b, c, d) : List (Bool × Bool × Bool × Bool)).toFinset = (Finset.univ : Finset (Bool × Bool × Bool × Bool)); decide +kernel)⟩
    }

noncomputable def facts_1 : Contract.SealFacts catalog_1 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyCausalFinite.local_bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_2 : Contract.SealCatalog := {
      arenaName := `Reg.Support.LegacyContextReplacement.objectArena
      catalogId := `Reg.Support.LegacyContextReplacement.objectArena
      arena := (_root_.Reg.Support.LegacyContextReplacement.objectArena)
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyContextReplacement.objectArena)).stateDecidableEq (Reg.Support.LegacyContextReplacement.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 8
      stateCardEq := by decide +kernel
      full := 0
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 56, uniqueEq := by decide +kernel, without := 56, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyContextReplacement.objectArena)).stateDecidableEq (Reg.Support.LegacyContextReplacement.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyContextReplacement.objectArena)).stateDecidableEq (Reg.Support.LegacyContextReplacement.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := by letI := ((_root_.Reg.Support.LegacyContextReplacement.objectArena)).stateFintype; letI := ((_root_.Reg.Support.LegacyContextReplacement.objectArena)).stateDecidableEq; exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩
    }

noncomputable def facts_2 : Contract.SealFacts catalog_2 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyContextReplacement.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_3 : Contract.SealCatalog := {
      arenaName := `Reg.Support.LegacyGluing.arena
      catalogId := `Reg.Support.LegacyGluing.arena
      arena := (_root_.Reg.Support.LegacyGluing.arena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyGluing.arena).toArena).stateDecidableEq (Reg.Support.LegacyGluing.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 8
      stateCardEq := by decide +kernel
      full := 8
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 48, uniqueEq := by decide +kernel, without := 56, withoutEq := by decide +kernel, roleBins := ![0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyGluing.arena).toArena).stateDecidableEq (Reg.Support.LegacyGluing.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyGluing.arena).toArena).stateDecidableEq (Reg.Support.LegacyGluing.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := by letI := ((_root_.Reg.Support.LegacyGluing.arena).toArena).stateFintype; letI := ((_root_.Reg.Support.LegacyGluing.arena).toArena).stateDecidableEq; exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩
    }

noncomputable def facts_3 : Contract.SealFacts catalog_3 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyGluing.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_4 : Contract.SealCatalog := {
      arenaName := `Reg.Support.LegacyResidue.arena
      catalogId := `Reg.Support.LegacyResidue.arena
      arena := (_root_.Reg.Support.LegacyResidue.arena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyResidue.arena).toArena).stateDecidableEq (Reg.Support.LegacyResidue.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 4
      stateCardEq := by decide +kernel
      full := 0
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 12, uniqueEq := by decide +kernel, without := 12, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyResidue.arena).toArena).stateDecidableEq (Reg.Support.LegacyResidue.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyResidue.arena).toArena).stateDecidableEq (Reg.Support.LegacyResidue.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := by letI := ((_root_.Reg.Support.LegacyResidue.arena).toArena).stateFintype; letI := ((_root_.Reg.Support.LegacyResidue.arena).toArena).stateDecidableEq; exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩
    }

noncomputable def facts_4 : Contract.SealFacts catalog_4 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyResidue.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_5 : Contract.SealCatalog := {
      arenaName := `Reg.Support.LegacyStaticDesign.arena
      catalogId := `Reg.Support.LegacyStaticDesign.arena
      arena := (_root_.Reg.Support.LegacyStaticDesign.arena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyStaticDesign.arena).toArena).stateDecidableEq (Reg.Support.LegacyStaticDesign.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 3
      stateCardEq := by decide +kernel
      full := 0
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 6, uniqueEq := by decide +kernel, without := 6, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyStaticDesign.arena).toArena).stateDecidableEq (Reg.Support.LegacyStaticDesign.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyStaticDesign.arena).toArena).stateDecidableEq (Reg.Support.LegacyStaticDesign.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := by letI := ((_root_.Reg.Support.LegacyStaticDesign.arena).toArena).stateFintype; letI := ((_root_.Reg.Support.LegacyStaticDesign.arena).toArena).stateDecidableEq; exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩
    }

noncomputable def facts_5 : Contract.SealFacts catalog_5 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyStaticDesign.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_6_units : Fin 1 → D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
    (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena) :=
  ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention) }]

noncomputable def catalog_6 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)
      size := 1
      units := catalog_6_units
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 32
      stateCardEq := by decide +kernel
      full := 24
      fullEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_6_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1; exact (catalog.fusedFull_eq_escapeNumerator states indices).symm.trans (by decide +kernel)
      rows := Fin.cases ({ unique := 968, uniqueEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_6_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1; exact (catalog.fusedUnique_eq_uniqueCaptureCount states indices (0 : Fin 1)).symm.trans (by decide +kernel), without := 992, withoutEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_6_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1; exact (catalog.fusedWithout_eq_escapeNumerator_without states indices (0 : Fin 1)).symm.trans (by decide +kernel), roleBins := ![0, 0, 0, 0, 0, 0, 0, 968, 0, 0, 0, 0, 0, 0, 0], roleEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_6_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1; exact fun bucket => (catalog.fusedRoleBins_eq_roleHistogram states indices (0 : Fin 1) bucket).symm.trans (congrFun (by decide +kernel : (catalog.fusedCounts states indices).roleBins (0 : Fin 1) = ![0, 0, 0, 0, 0, 0, 0, 968, 0, 0, 0, 0, 0, 0, 0]) bucket), roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_6_units).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_6_units).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.__state_enumeration
    }

noncomputable def facts_6 : Contract.SealFacts catalog_6 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_7 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.SystemUnit.systemRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 2
      stateCardEq := by decide +kernel
      full := 0
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 2, uniqueEq := by decide +kernel, without := 2, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.SystemUnit.systemRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.SystemUnit.systemRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).toArena).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).toArena).stateDecidableEq; exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩
    }

noncomputable def facts_7 : Contract.SealFacts catalog_7 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.SystemUnit.system_self_application_realization.toTheoremUnit
           D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_8 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange.commutingCompletionRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 4
      stateCardEq := by decide +kernel
      full := 0
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 12, uniqueEq := by decide +kernel, without := 12, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange.commutingCompletionRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange.commutingCompletionRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena).toArena).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena).toArena).stateDecidableEq; exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩
    }

noncomputable def facts_8 : Contract.SealFacts catalog_8 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange.commutativity_hypothesis_is_necessary_realization.toTheoremUnit
           D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_9 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 9
      stateCardEq := by decide +kernel
      full := 12
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 60, uniqueEq := by decide +kernel, without := 72, withoutEq := by decide +kernel, roleBins := ![0, 0, 12, 0, 0, 0, 0, 30, 0, 0, 18, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena).toArena).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena).toArena).stateDecidableEq; exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩
    }

noncomputable def facts_9 : Contract.SealFacts catalog_9 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_realization.toTheoremUnit
           D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_10 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena).toArena).stateDecidableEq (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutRealization D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) fun (atom : D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom) => Reg.Support.LegacySpectrum.indexReadout atom)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 5
      stateCardEq := by decide +kernel
      full := 0
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 20, uniqueEq := by decide +kernel, without := 20, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena).toArena).stateDecidableEq (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutRealization D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) fun (atom : D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom) => Reg.Support.LegacySpectrum.indexReadout atom)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena).toArena).stateDecidableEq (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutRealization D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) fun (atom : D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom) => Reg.Support.LegacySpectrum.indexReadout atom)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena).toArena).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena).toArena).stateDecidableEq; exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩
    }

noncomputable def facts_10 : Contract.SealFacts catalog_10 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacySpectrum.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective), correct := by rfl }]
             complete := rfl }

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.InformationRoot.SealedCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application), theoremName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena, statementIdentity := some "sha256:a3a2c21de13a5366dbb0d8ab39bc747e95b22c7cbeecb7ef39d86092b4c70ab0", registrationModuleName := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary), theoremName := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena, statementIdentity := some "sha256:1aed443dafdf76d41d4cca3a5a8bbf76e5a0f33e4a90453061b57fc3f432fb0a", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause), theoremName := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena, statementIdentity := some "sha256:b93e6bd918cabb38e32a21f11542a80c47dcc6ba73bdeac72336a5c75648c24c", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power), theoremName := `D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power, objectArenaName := `Reg.Support.LegacyAgenda.arena, statementIdentity := some "sha256:384a1edc32c16ec0b4045c373ce00d995b3fa571bb9cbf36960355b33a93cc00", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification), theoremName := `D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification, objectArenaName := `Reg.Support.LegacyResidue.arena, statementIdentity := some "sha256:6f8434c94b05962f830bd9c47522da114d168db8b17fa7825970bf48a600b9e6", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective), theoremName := `D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena, statementIdentity := some "sha256:970d0c4dbc3081113fb682ad75b2e6ee7f11e8330ded5624aa79599b799b76b3", registrationModuleName := `Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points), theoremName := `D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points, objectArenaName := `Reg.Support.LegacyContextReplacement.objectArena, statementIdentity := some "sha256:778398ffe72817b135e29453ae9a3b796de14383670686abbf230840cb7ee515", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual), theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual, objectArenaName := `Reg.Support.LegacyCausalCoordinates.icObjectArena, statementIdentity := some "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state), theoremName := `D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state, objectArenaName := `Reg.Support.LegacyGluing.arena, statementIdentity := some "sha256:95b576248df546ed3529c83c5c171a1ab2f6cff8fd9f78d7db83204dd4ecfb56", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention), theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena, statementIdentity := some "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design), theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design, objectArenaName := `Reg.Support.LegacyStaticDesign.arena, statementIdentity := some "sha256:408742a2c71557575944155350def43ed8f9f37ec3a19fe75f721e084dfe939a", registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.InformationRoot }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application), theoremName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena, statementIdentity := some "sha256:a3a2c21de13a5366dbb0d8ab39bc747e95b22c7cbeecb7ef39d86092b4c70ab0", registrationModuleName := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary), theoremName := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena, statementIdentity := some "sha256:1aed443dafdf76d41d4cca3a5a8bbf76e5a0f33e4a90453061b57fc3f432fb0a", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause), theoremName := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena, statementIdentity := some "sha256:b93e6bd918cabb38e32a21f11542a80c47dcc6ba73bdeac72336a5c75648c24c", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power), theoremName := `D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power, objectArenaName := `Reg.Support.LegacyAgenda.arena, statementIdentity := some "sha256:384a1edc32c16ec0b4045c373ce00d995b3fa571bb9cbf36960355b33a93cc00", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification), theoremName := `D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification, objectArenaName := `Reg.Support.LegacyResidue.arena, statementIdentity := some "sha256:6f8434c94b05962f830bd9c47522da114d168db8b17fa7825970bf48a600b9e6", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective), theoremName := `D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena, statementIdentity := some "sha256:970d0c4dbc3081113fb682ad75b2e6ee7f11e8330ded5624aa79599b799b76b3", registrationModuleName := `Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points), theoremName := `D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points, objectArenaName := `Reg.Support.LegacyContextReplacement.objectArena, statementIdentity := some "sha256:778398ffe72817b135e29453ae9a3b796de14383670686abbf230840cb7ee515", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual), theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual, objectArenaName := `Reg.Support.LegacyCausalCoordinates.icObjectArena, statementIdentity := some "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state), theoremName := `D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state, objectArenaName := `Reg.Support.LegacyGluing.arena, statementIdentity := some "sha256:95b576248df546ed3529c83c5c171a1ab2f6cff8fd9f78d7db83204dd4ecfb56", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention), theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena, statementIdentity := some "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design), theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design, objectArenaName := `Reg.Support.LegacyStaticDesign.arena, statementIdentity := some "sha256:408742a2c71557575944155350def43ed8f9f37ec3a19fe75f721e084dfe939a", registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual), theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual, objectArenaName := `Reg.Support.LegacyCausalCoordinates.objectArena, statementIdentity := some "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention), theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention, objectArenaName := `Reg.Support.LegacyCausalCoordinates.objectArena, statementIdentity := some "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration }],
  baseline := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application), theoremName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena, statementIdentity := some "sha256:a3a2c21de13a5366dbb0d8ab39bc747e95b22c7cbeecb7ef39d86092b4c70ab0", registrationModuleName := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary), theoremName := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena, statementIdentity := some "sha256:1aed443dafdf76d41d4cca3a5a8bbf76e5a0f33e4a90453061b57fc3f432fb0a", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause), theoremName := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena, statementIdentity := some "sha256:b93e6bd918cabb38e32a21f11542a80c47dcc6ba73bdeac72336a5c75648c24c", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power), theoremName := `D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power, objectArenaName := `Reg.Support.LegacyAgenda.arena, statementIdentity := some "sha256:384a1edc32c16ec0b4045c373ce00d995b3fa571bb9cbf36960355b33a93cc00", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification), theoremName := `D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification, objectArenaName := `Reg.Support.LegacyResidue.arena, statementIdentity := some "sha256:6f8434c94b05962f830bd9c47522da114d168db8b17fa7825970bf48a600b9e6", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective), theoremName := `D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena, statementIdentity := some "sha256:970d0c4dbc3081113fb682ad75b2e6ee7f11e8330ded5624aa79599b799b76b3", registrationModuleName := `Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points), theoremName := `D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points, objectArenaName := `Reg.Support.LegacyContextReplacement.objectArena, statementIdentity := some "sha256:778398ffe72817b135e29453ae9a3b796de14383670686abbf230840cb7ee515", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual), theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual, objectArenaName := `Reg.Support.LegacyCausalCoordinates.icObjectArena, statementIdentity := some "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state), theoremName := `D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state, objectArenaName := `Reg.Support.LegacyGluing.arena, statementIdentity := some "sha256:95b576248df546ed3529c83c5c171a1ab2f6cff8fd9f78d7db83204dd4ecfb56", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention), theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena, statementIdentity := some "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design), theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design, objectArenaName := `Reg.Support.LegacyStaticDesign.arena, statementIdentity := some "sha256:408742a2c71557575944155350def43ed8f9f37ec3a19fe75f721e084dfe939a", registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.InformationRoot }],
  companionPrefix := some `Reg.Catalogs.InformationRoot } }

noncomputable def view_0 : Contract.SealCatalogView := { catalog := catalog_0, facts := facts_0 }

noncomputable def view_1 : Contract.SealCatalogView := { catalog := catalog_1, facts := facts_1 }

noncomputable def view_2 : Contract.SealCatalogView := { catalog := catalog_2, facts := facts_2 }

noncomputable def view_3 : Contract.SealCatalogView := { catalog := catalog_3, facts := facts_3 }

noncomputable def view_4 : Contract.SealCatalogView := { catalog := catalog_4, facts := facts_4 }

noncomputable def view_5 : Contract.SealCatalogView := { catalog := catalog_5, facts := facts_5 }

noncomputable def view_6 : Contract.SealCatalogView := { catalog := catalog_6, facts := facts_6 }

noncomputable def view_7 : Contract.SealCatalogView := { catalog := catalog_7, facts := facts_7 }

noncomputable def view_8 : Contract.SealCatalogView := { catalog := catalog_8, facts := facts_8 }

noncomputable def view_9 : Contract.SealCatalogView := { catalog := catalog_9, facts := facts_9 }

noncomputable def view_10 : Contract.SealCatalogView := { catalog := catalog_10, facts := facts_10 }

noncomputable def «seal» : Contract.Seal := {
  rootId := `Reg.Catalogs.InformationRoot.SealedCatalog
  catalogs := #[
    view_0,
    view_1,
    view_2,
    view_3,
    view_4,
    view_5,
    view_6,
    view_7,
    view_8,
    view_9,
    view_10
  ]
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxRecDepth, value := .nat 100000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.Catalogs.InformationRoot.SealedCatalog
