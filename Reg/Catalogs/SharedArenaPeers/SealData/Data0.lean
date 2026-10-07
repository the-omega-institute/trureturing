import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Basic
import Mathlib.Tactic.FinCases
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.CIRPT.PrimitiveKernel
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
import D5.S3.ConceptDynamics.InformationEscape.StructuralNovelty
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Fused
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion
import D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
import D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
import D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative
import Reg.Catalogs.SharedArenaPeers.SealData.States0

namespace Reg.Catalogs.SharedArenaPeers.SealedCatalog
open LeanInformationAudit

noncomputable def catalog_0_units : Fin 5 → D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
    (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena) :=
  ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not) }]

noncomputable def catalog_0 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena
      catalogId := `finiteProbe
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)
      size := 5
      units := catalog_0_units
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 16
      stateCardEq := by decide +kernel
      full := 0
      fullEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 5; exact (catalog.fusedFull_eq_escapeNumerator states indices).symm.trans (by decide +kernel)
      rows := Fin.cases ({ unique := 0, uniqueEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 5; exact (catalog.fusedUnique_eq_uniqueCaptureCount states indices (0 : Fin 5)).symm.trans (by decide +kernel), without := 0, withoutEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 5; exact (catalog.fusedWithout_eq_escapeNumerator_without states indices (0 : Fin 5)).symm.trans (by decide +kernel), roleBins := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], roleEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 5; exact fun bucket => (catalog.fusedRoleBins_eq_roleHistogram states indices (0 : Fin 5) bucket).symm.trans (congrFun (by decide +kernel : (catalog.fusedCounts states indices).roleBins (0 : Fin 5) = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) bucket), roleTotal := by decide +kernel, conclusion := .zero rfl (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel) (by exact of_not_not ((not_congr ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units).lowersEscape_iff_not_mem_semanticClosureWithout 0 (by decide +kernel))).mp (((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units).trivialInCatalog_iff_not_lowersEscape 0 (by decide +kernel)).mp (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel)))) }) (Fin.cases ({ unique := 0, uniqueEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 5; exact (catalog.fusedUnique_eq_uniqueCaptureCount states indices (1 : Fin 5)).symm.trans (by decide +kernel), without := 0, withoutEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 5; exact (catalog.fusedWithout_eq_escapeNumerator_without states indices (1 : Fin 5)).symm.trans (by decide +kernel), roleBins := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], roleEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 5; exact fun bucket => (catalog.fusedRoleBins_eq_roleHistogram states indices (1 : Fin 5) bucket).symm.trans (congrFun (by decide +kernel : (catalog.fusedCounts states indices).roleBins (1 : Fin 5) = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) bucket), roleTotal := by decide +kernel, conclusion := .zero rfl (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel) (by exact of_not_not ((not_congr ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units).lowersEscape_iff_not_mem_semanticClosureWithout 1 (by decide +kernel))).mp (((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units).trivialInCatalog_iff_not_lowersEscape 1 (by decide +kernel)).mp (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel)))) }) (Fin.cases ({ unique := 0, uniqueEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 5; exact (catalog.fusedUnique_eq_uniqueCaptureCount states indices (2 : Fin 5)).symm.trans (by decide +kernel), without := 0, withoutEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 5; exact (catalog.fusedWithout_eq_escapeNumerator_without states indices (2 : Fin 5)).symm.trans (by decide +kernel), roleBins := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], roleEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 5; exact fun bucket => (catalog.fusedRoleBins_eq_roleHistogram states indices (2 : Fin 5) bucket).symm.trans (congrFun (by decide +kernel : (catalog.fusedCounts states indices).roleBins (2 : Fin 5) = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) bucket), roleTotal := by decide +kernel, conclusion := .zero rfl (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel) (by exact of_not_not ((not_congr ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units).lowersEscape_iff_not_mem_semanticClosureWithout 2 (by decide +kernel))).mp (((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units).trivialInCatalog_iff_not_lowersEscape 2 (by decide +kernel)).mp (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel)))) }) (Fin.cases ({ unique := 0, uniqueEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 5; exact (catalog.fusedUnique_eq_uniqueCaptureCount states indices (3 : Fin 5)).symm.trans (by decide +kernel), without := 0, withoutEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 5; exact (catalog.fusedWithout_eq_escapeNumerator_without states indices (3 : Fin 5)).symm.trans (by decide +kernel), roleBins := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], roleEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 5; exact fun bucket => (catalog.fusedRoleBins_eq_roleHistogram states indices (3 : Fin 5) bucket).symm.trans (congrFun (by decide +kernel : (catalog.fusedCounts states indices).roleBins (3 : Fin 5) = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) bucket), roleTotal := by decide +kernel, conclusion := .zero rfl (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel) (by exact of_not_not ((not_congr ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units).lowersEscape_iff_not_mem_semanticClosureWithout 3 (by decide +kernel))).mp (((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units).trivialInCatalog_iff_not_lowersEscape 3 (by decide +kernel)).mp (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel)))) }) (Fin.cases ({ unique := 0, uniqueEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 5; exact (catalog.fusedUnique_eq_uniqueCaptureCount states indices (4 : Fin 5)).symm.trans (by decide +kernel), without := 0, withoutEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 5; exact (catalog.fusedWithout_eq_escapeNumerator_without states indices (4 : Fin 5)).symm.trans (by decide +kernel), roleBins := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], roleEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 5; exact fun bucket => (catalog.fusedRoleBins_eq_roleHistogram states indices (4 : Fin 5) bucket).symm.trans (congrFun (by decide +kernel : (catalog.fusedCounts states indices).roleBins (4 : Fin 5) = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) bucket), roleTotal := by decide +kernel, conclusion := .zero rfl (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel) (by exact of_not_not ((not_congr ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units).lowersEscape_iff_not_mem_semanticClosureWithout 4 (by decide +kernel))).mp (((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_0_units).trivialInCatalog_iff_not_lowersEscape 4 (by decide +kernel)).mp (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel)))) }) (fun i => Fin.elim0 i)))))
      collisions := #[⟨⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨by decide +kernel, by constructor <;> decide +kernel⟩⟩, ⟨⟨0, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨by decide +kernel, by constructor <;> decide +kernel⟩⟩, ⟨⟨0, by decide +kernel⟩, ⟨3, by decide +kernel⟩, ⟨by decide +kernel, by constructor <;> decide +kernel⟩⟩, ⟨⟨0, by decide +kernel⟩, ⟨4, by decide +kernel⟩, ⟨by decide +kernel, by constructor <;> decide +kernel⟩⟩]
      conclusion := .redundant (by exact ⟨0, by decide +kernel⟩)
      enumeration := {
        states := ([(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15)] : List (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
        nodup := by letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateFintype; change ([(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15)] : List (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)).Nodup; apply of_decide_eq_true; decide +kernel
        complete := by letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena)).stateFintype; change ([(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15)] : List (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)).toFinset = (Finset.univ : Finset (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)); apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_0 : Contract.SealFacts catalog_0 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteNotIdentifiable_bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable), correct := by rfl }, { position := 1, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteFiber_bridge.toTheoremUnit
                          D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber), correct := by rfl }, { position := 2, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteFiner_bridge.toTheoremUnit
                                                                 D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer), correct := by rfl }, { position := 3, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteIntervention_bridge.toTheoremUnit
                                                                         D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual), correct := by rfl }, { position := 4, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteTarget_bridge.toTheoremUnit
                                                                                            D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 0
        uniqueEq := ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq).trans (by rfl)
        without := 0
        withoutEq := ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .zero rfl (by
            unfold D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog
            apply Finset.card_eq_zero.mp
            exact (catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq) (by
          apply of_not_not
          exact (not_congr (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_not_mem_semanticClosureWithout _ _ catalog_0.nondegenerate)).mp
            ((D5.S3.ConceptDynamics.InformationEscape.Catalog.trivialInCatalog_iff_not_lowersEscape _ _ catalog_0.nondegenerate).mp (by
            unfold D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog
            apply Finset.card_eq_zero.mp
            exact (catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq))) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 8, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 9, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 10, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 11, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 12, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 13, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 14, within := by decide +kernel, item := 0, correct := by decide +kernel }]
                complete := rfl }
      axes := { rows := [{ index := by change Sum _ _; exact (@Sum.inl
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
                 D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
                 (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
                   D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                 D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
                 (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
                   D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
               Bool.true), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.false), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.false)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.false)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (state_0), classId := 0 },
                       { item := (state_1), classId := 1 },
                       { item := (state_2), classId := 2 },
                       { item := (state_3), classId := 3 },
                       { item := (state_4), classId := 4 },
                       { item := (state_5), classId := 5 },
                       { item := (state_6), classId := 6 },
                       { item := (state_7), classId := 7 },
                       { item := (state_8), classId := 8 },
                       { item := (state_9), classId := 9 },
                       { item := (state_10), classId := 10 },
                       { item := (state_11), classId := 11 },
                       { item := (state_12), classId := 12 },
                       { item := (state_13), classId := 13 },
                       { item := (state_14), classId := 14 },
                       { item := (state_15), classId := 15 }]
                     nodup := by
                       letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateFintype
                       change ([(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15)] : List (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateFintype
                       change ∀ x : (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM), x ∈ [(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl },
    {
      position := 1
      within := by decide +kernel
      row := {
        unique := 0
        uniqueEq := ((catalog_0.rows (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq).trans (by rfl)
        without := 0
        withoutEq := ((catalog_0.rows (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_0.rows (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_0.rows (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .zero rfl (by
            unfold D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog
            apply Finset.card_eq_zero.mp
            exact (catalog_0.rows (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq) (by
          apply of_not_not
          exact (not_congr (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_not_mem_semanticClosureWithout _ _ catalog_0.nondegenerate)).mp
            ((D5.S3.ConceptDynamics.InformationEscape.Catalog.trivialInCatalog_iff_not_lowersEscape _ _ catalog_0.nondegenerate).mp (by
            unfold D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog
            apply Finset.card_eq_zero.mp
            exact (catalog_0.rows (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq))) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 8, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 9, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 10, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 11, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 12, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 13, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 14, within := by decide +kernel, item := 0, correct := by decide +kernel }]
                complete := rfl }
      axes := { rows := [{ index := by change Sum _ _; exact (@Sum.inl
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
                 D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
                 (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
                   D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                 D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
                 (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
                   D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
               Bool.true), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.false), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.false)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.false)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (state_0), classId := 0 },
                       { item := (state_1), classId := 1 },
                       { item := (state_2), classId := 2 },
                       { item := (state_3), classId := 3 },
                       { item := (state_4), classId := 4 },
                       { item := (state_5), classId := 5 },
                       { item := (state_6), classId := 6 },
                       { item := (state_7), classId := 7 },
                       { item := (state_8), classId := 8 },
                       { item := (state_9), classId := 9 },
                       { item := (state_10), classId := 10 },
                       { item := (state_11), classId := 11 },
                       { item := (state_12), classId := 12 },
                       { item := (state_13), classId := 13 },
                       { item := (state_14), classId := 14 },
                       { item := (state_15), classId := 15 }]
                     nodup := by
                       letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateFintype
                       change ([(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15)] : List (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateFintype
                       change ∀ x : (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM), x ∈ [(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl },
    {
      position := 2
      within := by decide +kernel
      row := {
        unique := 0
        uniqueEq := ((catalog_0.rows (⟨2, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq).trans (by rfl)
        without := 0
        withoutEq := ((catalog_0.rows (⟨2, by decide +kernel⟩ : Fin catalog_0.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_0.rows (⟨2, by decide +kernel⟩ : Fin catalog_0.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_0.rows (⟨2, by decide +kernel⟩ : Fin catalog_0.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .zero rfl (by
            unfold D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog
            apply Finset.card_eq_zero.mp
            exact (catalog_0.rows (⟨2, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq) (by
          apply of_not_not
          exact (not_congr (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_not_mem_semanticClosureWithout _ _ catalog_0.nondegenerate)).mp
            ((D5.S3.ConceptDynamics.InformationEscape.Catalog.trivialInCatalog_iff_not_lowersEscape _ _ catalog_0.nondegenerate).mp (by
            unfold D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog
            apply Finset.card_eq_zero.mp
            exact (catalog_0.rows (⟨2, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq))) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 8, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 9, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 10, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 11, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 12, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 13, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 14, within := by decide +kernel, item := 0, correct := by decide +kernel }]
                complete := rfl }
      axes := { rows := [{ index := by change Sum _ _; exact (@Sum.inl
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
                 D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
                 (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
                   D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                 D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
                 (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
                   D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
               Bool.true), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.false), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.false)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨2, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨2, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨2, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨2, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.false)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨2, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨2, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨2, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨2, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (state_0), classId := 0 },
                       { item := (state_1), classId := 1 },
                       { item := (state_2), classId := 2 },
                       { item := (state_3), classId := 3 },
                       { item := (state_4), classId := 4 },
                       { item := (state_5), classId := 5 },
                       { item := (state_6), classId := 6 },
                       { item := (state_7), classId := 7 },
                       { item := (state_8), classId := 8 },
                       { item := (state_9), classId := 9 },
                       { item := (state_10), classId := 10 },
                       { item := (state_11), classId := 11 },
                       { item := (state_12), classId := 12 },
                       { item := (state_13), classId := 13 },
                       { item := (state_14), classId := 14 },
                       { item := (state_15), classId := 15 }]
                     nodup := by
                       letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateFintype
                       change ([(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15)] : List (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateFintype
                       change ∀ x : (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM), x ∈ [(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl },
    {
      position := 3
      within := by decide +kernel
      row := {
        unique := 0
        uniqueEq := ((catalog_0.rows (⟨3, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq).trans (by rfl)
        without := 0
        withoutEq := ((catalog_0.rows (⟨3, by decide +kernel⟩ : Fin catalog_0.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_0.rows (⟨3, by decide +kernel⟩ : Fin catalog_0.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_0.rows (⟨3, by decide +kernel⟩ : Fin catalog_0.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .zero rfl (by
            unfold D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog
            apply Finset.card_eq_zero.mp
            exact (catalog_0.rows (⟨3, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq) (by
          apply of_not_not
          exact (not_congr (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_not_mem_semanticClosureWithout _ _ catalog_0.nondegenerate)).mp
            ((D5.S3.ConceptDynamics.InformationEscape.Catalog.trivialInCatalog_iff_not_lowersEscape _ _ catalog_0.nondegenerate).mp (by
            unfold D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog
            apply Finset.card_eq_zero.mp
            exact (catalog_0.rows (⟨3, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq))) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 8, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 9, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 10, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 11, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 12, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 13, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 14, within := by decide +kernel, item := 0, correct := by decide +kernel }]
                complete := rfl }
      axes := { rows := [{ index := by change Sum _ _; exact (@Sum.inl
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
                 D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
                 (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
                   D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                 D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
                 (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
                   D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
               Bool.true), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.false), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.false)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨3, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨3, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨3, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨3, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.false)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨3, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨3, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨3, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨3, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (state_0), classId := 0 },
                       { item := (state_1), classId := 1 },
                       { item := (state_2), classId := 2 },
                       { item := (state_3), classId := 3 },
                       { item := (state_4), classId := 4 },
                       { item := (state_5), classId := 5 },
                       { item := (state_6), classId := 6 },
                       { item := (state_7), classId := 7 },
                       { item := (state_8), classId := 8 },
                       { item := (state_9), classId := 9 },
                       { item := (state_10), classId := 10 },
                       { item := (state_11), classId := 11 },
                       { item := (state_12), classId := 12 },
                       { item := (state_13), classId := 13 },
                       { item := (state_14), classId := 14 },
                       { item := (state_15), classId := 15 }]
                     nodup := by
                       letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateFintype
                       change ([(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15)] : List (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateFintype
                       change ∀ x : (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM), x ∈ [(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl },
    {
      position := 4
      within := by decide +kernel
      row := {
        unique := 0
        uniqueEq := ((catalog_0.rows (⟨4, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq).trans (by rfl)
        without := 0
        withoutEq := ((catalog_0.rows (⟨4, by decide +kernel⟩ : Fin catalog_0.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_0.rows (⟨4, by decide +kernel⟩ : Fin catalog_0.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_0.rows (⟨4, by decide +kernel⟩ : Fin catalog_0.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .zero rfl (by
            unfold D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog
            apply Finset.card_eq_zero.mp
            exact (catalog_0.rows (⟨4, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq) (by
          apply of_not_not
          exact (not_congr (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_not_mem_semanticClosureWithout _ _ catalog_0.nondegenerate)).mp
            ((D5.S3.ConceptDynamics.InformationEscape.Catalog.trivialInCatalog_iff_not_lowersEscape _ _ catalog_0.nondegenerate).mp (by
            unfold D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog
            apply Finset.card_eq_zero.mp
            exact (catalog_0.rows (⟨4, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq))) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 8, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 9, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 10, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 11, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 12, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 13, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 14, within := by decide +kernel, item := 0, correct := by decide +kernel }]
                complete := rfl }
      axes := { rows := [{ index := by change Sum _ _; exact (@Sum.inl
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
                 D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
                 (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
                   D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                 D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
                 (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
                   D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
               Bool.true), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.false), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.false)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨4, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨4, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨4, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨4, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM))
          Bool.false)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨4, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨4, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨4, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨4, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (state_0), classId := 0 },
                       { item := (state_1), classId := 1 },
                       { item := (state_2), classId := 2 },
                       { item := (state_3), classId := 3 },
                       { item := (state_4), classId := 4 },
                       { item := (state_5), classId := 5 },
                       { item := (state_6), classId := 6 },
                       { item := (state_7), classId := 7 },
                       { item := (state_8), classId := 8 },
                       { item := (state_9), classId := 9 },
                       { item := (state_10), classId := 10 },
                       { item := (state_11), classId := 11 },
                       { item := (state_12), classId := 12 },
                       { item := (state_13), classId := 13 },
                       { item := (state_14), classId := 14 },
                       { item := (state_15), classId := 15 }]
                     nodup := by
                       letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateFintype
                       change ([(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15)] : List (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateFintype
                       change ∀ x : (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM), x ∈ [(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) := catalog_0.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

end Reg.Catalogs.SharedArenaPeers.SealedCatalog
