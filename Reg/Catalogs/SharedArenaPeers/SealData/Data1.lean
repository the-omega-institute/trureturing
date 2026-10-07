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
import D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness
import D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
import Reg.Catalogs.SharedArenaPeers.SealData.States0
import Reg.Catalogs.SharedArenaPeers.SealData.States1
import Reg.Catalogs.SharedArenaPeers.SealData.States2
import Reg.Catalogs.SharedArenaPeers.SealData.States3
import Reg.Catalogs.SharedArenaPeers.SealData.States4
import Reg.Catalogs.SharedArenaPeers.SealData.States5
import Reg.Catalogs.SharedArenaPeers.SealData.States6
import Reg.Catalogs.SharedArenaPeers.SealData.States7
import Reg.Catalogs.SharedArenaPeers.SealData.States8

namespace Reg.Catalogs.SharedArenaPeers.SealedCatalog
open LeanInformationAudit

noncomputable def catalog_1_units : Fin 2 → D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
    (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena) :=
  ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention) }]

noncomputable def catalog_1 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena
      catalogId := `finiteProbe
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)
      size := 2
      units := catalog_1_units
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 32
      stateCardEq := by decide +kernel
      full := 24
      fullEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_1_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 2; exact (catalog.fusedFull_eq_escapeNumerator states indices).symm.trans (by decide +kernel)
      rows := Fin.cases ({ unique := 0, uniqueEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_1_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 2; exact (catalog.fusedUnique_eq_uniqueCaptureCount states indices (0 : Fin 2)).symm.trans (by decide +kernel), without := 24, withoutEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_1_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 2; exact (catalog.fusedWithout_eq_escapeNumerator_without states indices (0 : Fin 2)).symm.trans (by decide +kernel), roleBins := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], roleEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_1_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 2; exact fun bucket => (catalog.fusedRoleBins_eq_roleHistogram states indices (0 : Fin 2) bucket).symm.trans (congrFun (by decide +kernel : (catalog.fusedCounts states indices).roleBins (0 : Fin 2) = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) bucket), roleTotal := by decide +kernel, conclusion := .zero rfl (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel) (by exact of_not_not ((not_congr ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_1_units).lowersEscape_iff_not_mem_semanticClosureWithout 0 (by decide +kernel))).mp (((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_1_units).trivialInCatalog_iff_not_lowersEscape 0 (by decide +kernel)).mp (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel)))) }) (Fin.cases ({ unique := 0, uniqueEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_1_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 2; exact (catalog.fusedUnique_eq_uniqueCaptureCount states indices (1 : Fin 2)).symm.trans (by decide +kernel), without := 24, withoutEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_1_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 2; exact (catalog.fusedWithout_eq_escapeNumerator_without states indices (1 : Fin 2)).symm.trans (by decide +kernel), roleBins := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], roleEq := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq; let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena) := _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.__state_enumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_1_units; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 2; exact fun bucket => (catalog.fusedRoleBins_eq_roleHistogram states indices (1 : Fin 2) bucket).symm.trans (congrFun (by decide +kernel : (catalog.fusedCounts states indices).roleBins (1 : Fin 2) = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) bucket), roleTotal := by decide +kernel, conclusion := .zero rfl (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel) (by exact of_not_not ((not_congr ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_1_units).lowersEscape_iff_not_mem_semanticClosureWithout 1 (by decide +kernel))).mp (((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector catalog_1_units).trivialInCatalog_iff_not_lowersEscape 1 (by decide +kernel)).mp (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel)))) }) (fun i => Fin.elim0 i))
      collisions := #[⟨⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨by decide +kernel, by constructor <;> decide +kernel⟩⟩]
      conclusion := .redundant (by exact ⟨0, by decide +kernel⟩)
      enumeration := {
        states := ([(state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (state_26), (state_27), (state_28), (state_29), (state_30), (state_31), (state_32), (state_33), (state_34), (state_35), (state_36), (state_37), (state_38), (state_39), (state_40), (state_41), (state_42), (state_43), (state_44), (state_45), (state_46), (state_47)] : List (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
        nodup := by letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateFintype; change ([(state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (state_26), (state_27), (state_28), (state_29), (state_30), (state_31), (state_32), (state_33), (state_34), (state_35), (state_36), (state_37), (state_38), (state_39), (state_40), (state_41), (state_42), (state_43), (state_44), (state_45), (state_46), (state_47)] : List (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)).Nodup; apply of_decide_eq_true; decide +kernel
        complete := by letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateFintype; change ([(state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (state_26), (state_27), (state_28), (state_29), (state_30), (state_31), (state_32), (state_33), (state_34), (state_35), (state_36), (state_37), (state_38), (state_39), (state_40), (state_41), (state_42), (state_43), (state_44), (state_45), (state_46), (state_47)] : List (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)).toFinset = (Finset.univ : Finset (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)); apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_1 : Contract.SealFacts catalog_1 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteProfile_bridge.toTheoremUnit
           D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation), correct := by rfl }, { position := 1, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_bridge.toTheoremUnit
                                                 D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 0
        uniqueEq := ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).uniqueEq).trans (by rfl)
        without := 24
        withoutEq := ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .zero rfl (by
            unfold D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog
            apply Finset.card_eq_zero.mp
            exact (catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).uniqueEq) (by
          apply of_not_not
          exact (not_congr (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_not_mem_semanticClosureWithout _ _ catalog_1.nondegenerate)).mp
            ((D5.S3.ConceptDynamics.InformationEscape.Catalog.trivialInCatalog_iff_not_lowersEscape _ _ catalog_1.nondegenerate).mp (by
            unfold D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog
            apply Finset.card_eq_zero.mp
            exact (catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).uniqueEq))) }
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
                 D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
                 (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
                   D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                 D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
                 (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
                   D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
               Bool.true), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          Bool.false), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          Bool.false)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          Bool.false)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (state_16), classId := 0 },
                       { item := (state_17), classId := 1 },
                       { item := (state_18), classId := 2 },
                       { item := (state_19), classId := 3 },
                       { item := (state_20), classId := 4 },
                       { item := (state_21), classId := 5 },
                       { item := (state_22), classId := 6 },
                       { item := (state_23), classId := 7 },
                       { item := (state_24), classId := 8 },
                       { item := (state_25), classId := 9 },
                       { item := (state_26), classId := 10 },
                       { item := (state_27), classId := 11 },
                       { item := (state_28), classId := 12 },
                       { item := (state_29), classId := 13 },
                       { item := (state_30), classId := 14 },
                       { item := (state_31), classId := 15 },
                       { item := (state_32), classId := 0 },
                       { item := (state_33), classId := 0 },
                       { item := (state_34), classId := 12 },
                       { item := (state_35), classId := 12 },
                       { item := (state_36), classId := 16 },
                       { item := (state_37), classId := 17 },
                       { item := (state_38), classId := 18 },
                       { item := (state_39), classId := 19 },
                       { item := (state_40), classId := 20 },
                       { item := (state_41), classId := 21 },
                       { item := (state_42), classId := 22 },
                       { item := (state_43), classId := 23 },
                       { item := (state_44), classId := 3 },
                       { item := (state_45), classId := 15 },
                       { item := (state_46), classId := 3 },
                       { item := (state_47), classId := 15 }]
                     nodup := by
                       letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_1.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_1.arena.stateFintype
                       change ([(state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (state_26), (state_27), (state_28), (state_29), (state_30), (state_31), (state_32), (state_33), (state_34), (state_35), (state_36), (state_37), (state_38), (state_39), (state_40), (state_41), (state_42), (state_43), (state_44), (state_45), (state_46), (state_47)] : List (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_1.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_1.arena.stateFintype
                       change ∀ x : (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM), x ∈ [(state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (state_26), (state_27), (state_28), (state_29), (state_30), (state_31), (state_32), (state_33), (state_34), (state_35), (state_36), (state_37), (state_38), (state_39), (state_40), (state_41), (state_42), (state_43), (state_44), (state_45), (state_46), (state_47)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_1.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_1.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl },
    {
      position := 1
      within := by decide +kernel
      row := {
        unique := 0
        uniqueEq := ((catalog_1.rows (⟨1, by decide +kernel⟩ : Fin catalog_1.size)).uniqueEq).trans (by rfl)
        without := 24
        withoutEq := ((catalog_1.rows (⟨1, by decide +kernel⟩ : Fin catalog_1.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_1.rows (⟨1, by decide +kernel⟩ : Fin catalog_1.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_1.rows (⟨1, by decide +kernel⟩ : Fin catalog_1.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .zero rfl (by
            unfold D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog
            apply Finset.card_eq_zero.mp
            exact (catalog_1.rows (⟨1, by decide +kernel⟩ : Fin catalog_1.size)).uniqueEq) (by
          apply of_not_not
          exact (not_congr (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_not_mem_semanticClosureWithout _ _ catalog_1.nondegenerate)).mp
            ((D5.S3.ConceptDynamics.InformationEscape.Catalog.trivialInCatalog_iff_not_lowersEscape _ _ catalog_1.nondegenerate).mp (by
            unfold D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog
            apply Finset.card_eq_zero.mp
            exact (catalog_1.rows (⟨1, by decide +kernel⟩ : Fin catalog_1.size)).uniqueEq))) }
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
                 D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
                 (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
                   D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                 D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
                 (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
                   D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
               Bool.true), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          Bool.false), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          Bool.false)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_1.units (⟨1, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨1, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_1.units (⟨1, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨1, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.finiteSignature
              D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
          Bool.false)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_1.units (⟨1, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨1, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_1.units (⟨1, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨1, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (state_16), classId := 0 },
                       { item := (state_17), classId := 1 },
                       { item := (state_18), classId := 2 },
                       { item := (state_19), classId := 3 },
                       { item := (state_20), classId := 4 },
                       { item := (state_21), classId := 5 },
                       { item := (state_22), classId := 6 },
                       { item := (state_23), classId := 7 },
                       { item := (state_24), classId := 8 },
                       { item := (state_25), classId := 9 },
                       { item := (state_26), classId := 10 },
                       { item := (state_27), classId := 11 },
                       { item := (state_28), classId := 12 },
                       { item := (state_29), classId := 13 },
                       { item := (state_30), classId := 14 },
                       { item := (state_31), classId := 15 },
                       { item := (state_32), classId := 0 },
                       { item := (state_33), classId := 0 },
                       { item := (state_34), classId := 12 },
                       { item := (state_35), classId := 12 },
                       { item := (state_36), classId := 16 },
                       { item := (state_37), classId := 17 },
                       { item := (state_38), classId := 18 },
                       { item := (state_39), classId := 19 },
                       { item := (state_40), classId := 20 },
                       { item := (state_41), classId := 21 },
                       { item := (state_42), classId := 22 },
                       { item := (state_43), classId := 23 },
                       { item := (state_44), classId := 3 },
                       { item := (state_45), classId := 15 },
                       { item := (state_46), classId := 3 },
                       { item := (state_47), classId := 15 }]
                     nodup := by
                       letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_1.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_1.arena.stateFintype
                       change ([(state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (state_26), (state_27), (state_28), (state_29), (state_30), (state_31), (state_32), (state_33), (state_34), (state_35), (state_36), (state_37), (state_38), (state_39), (state_40), (state_41), (state_42), (state_43), (state_44), (state_45), (state_46), (state_47)] : List (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_1.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_1.arena.stateFintype
                       change ∀ x : (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM), x ∈ [(state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (state_26), (state_27), (state_28), (state_29), (state_30), (state_31), (state_32), (state_33), (state_34), (state_35), (state_36), (state_37), (state_38), (state_39), (state_40), (state_41), (state_42), (state_43), (state_44), (state_45), (state_46), (state_47)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_1.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_1.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

end Reg.Catalogs.SharedArenaPeers.SealedCatalog
