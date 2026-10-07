import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.CIRPT.PrimitiveKernel
import D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
import D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
import D5.S3.ConceptDynamics.InformationEscape.SystemUnit
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange
import D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
import D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
import D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
import Reg.Catalogs.InformationRoot.SealData.Data1
import Reg.Catalogs.InformationRoot.SealData.States0
import Reg.Catalogs.InformationRoot.SealData.States1
import Reg.Catalogs.InformationRoot.SealData.States10
import Reg.Catalogs.InformationRoot.SealData.States11
import Reg.Catalogs.InformationRoot.SealData.States12
import Reg.Catalogs.InformationRoot.SealData.States13
import Reg.Catalogs.InformationRoot.SealData.States14
import Reg.Catalogs.InformationRoot.SealData.States15
import Reg.Catalogs.InformationRoot.SealData.States16
import Reg.Catalogs.InformationRoot.SealData.States2
import Reg.Catalogs.InformationRoot.SealData.States3
import Reg.Catalogs.InformationRoot.SealData.States4
import Reg.Catalogs.InformationRoot.SealData.States5
import Reg.Catalogs.InformationRoot.SealData.States6
import Reg.Catalogs.InformationRoot.SealData.States7
import Reg.Catalogs.InformationRoot.SealData.States8
import Reg.Catalogs.InformationRoot.SealData.States9
import Reg.Support.LegacySpectrum

namespace Reg.Catalogs.InformationRoot.SealedCatalog
open LeanInformationAudit

noncomputable def facts_6 : Contract.SealFacts catalog_6 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 968
        uniqueEq := ((catalog_6.rows (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).uniqueEq).trans (by rfl)
        without := 992
        withoutEq := ((catalog_6.rows (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 968, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_6.rows (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_6.rows (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 968, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_6.nondegenerate).mpr
          rw [(catalog_6.rows (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).uniqueEq]
          decide +kernel) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 968, correct := by decide +kernel },
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_6.units (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).primitives.Index); exact (catalog_6.units (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_6.units (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).primitives.Index); exact (catalog_6.units (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).primitives.indexFintype)
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_6.units (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).primitives.Index); exact (catalog_6.units (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_6.units (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).primitives.Index); exact (catalog_6.units (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (state_27), classId := 0 },
                       { item := (state_28), classId := 1 },
                       { item := (state_29), classId := 2 },
                       { item := (state_30), classId := 3 },
                       { item := (state_31), classId := 4 },
                       { item := (state_32), classId := 5 },
                       { item := (state_33), classId := 6 },
                       { item := (state_34), classId := 7 },
                       { item := (state_35), classId := 8 },
                       { item := (state_36), classId := 9 },
                       { item := (state_37), classId := 10 },
                       { item := (state_38), classId := 11 },
                       { item := (state_39), classId := 12 },
                       { item := (state_40), classId := 13 },
                       { item := (state_41), classId := 14 },
                       { item := (state_42), classId := 15 },
                       { item := (state_43), classId := 0 },
                       { item := (state_44), classId := 0 },
                       { item := (state_45), classId := 12 },
                       { item := (state_46), classId := 12 },
                       { item := (state_47), classId := 16 },
                       { item := (state_48), classId := 17 },
                       { item := (state_49), classId := 18 },
                       { item := (state_50), classId := 19 },
                       { item := (state_51), classId := 20 },
                       { item := (state_52), classId := 21 },
                       { item := (state_53), classId := 22 },
                       { item := (state_54), classId := 23 },
                       { item := (state_55), classId := 3 },
                       { item := (state_56), classId := 15 },
                       { item := (state_57), classId := 3 },
                       { item := (state_58), classId := 15 }]
                     nodup := by
                       letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_6.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_6.arena.stateFintype
                       change ([(state_27), (state_28), (state_29), (state_30), (state_31), (state_32), (state_33), (state_34), (state_35), (state_36), (state_37), (state_38), (state_39), (state_40), (state_41), (state_42), (state_43), (state_44), (state_45), (state_46), (state_47), (state_48), (state_49), (state_50), (state_51), (state_52), (state_53), (state_54), (state_55), (state_56), (state_57), (state_58)] : List (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_6.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_6.arena.stateFintype
                       change ∀ x : (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM), x ∈ [(state_27), (state_28), (state_29), (state_30), (state_31), (state_32), (state_33), (state_34), (state_35), (state_36), (state_37), (state_38), (state_39), (state_40), (state_41), (state_42), (state_43), (state_44), (state_45), (state_46), (state_47), (state_48), (state_49), (state_50), (state_51), (state_52), (state_53), (state_54), (state_55), (state_56), (state_57), (state_58)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_6.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_6.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

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
      enumeration := {
        states := ([(Bool.true), (Bool.false)] : List (Bool))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_7 : Contract.SealFacts catalog_7 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.SystemUnit.system_self_application_realization.toTheoremUnit
           D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 2
        uniqueEq := ((catalog_7.rows (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).uniqueEq).trans (by rfl)
        without := 2
        withoutEq := ((catalog_7.rows (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_7.rows (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_7.rows (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_7.nondegenerate).mpr
          rw [(catalog_7.rows (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).uniqueEq]
          decide +kernel) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 2, correct := by decide +kernel },
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
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.State
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.signature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.State
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.signature)
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (nat_lit 0)
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.State
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.signature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.State
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.signature)
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (nat_lit 0)
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.State
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.signature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.State
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.signature))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_7.units (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).primitives.Index); exact (catalog_7.units (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_7.units (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).primitives.Index); exact (catalog_7.units (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.State
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.signature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.State
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.signature)), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.State
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.signature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.State
            D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.signature)
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (nat_lit 0)
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_7.units (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).primitives.Index); exact (catalog_7.units (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_7.units (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).primitives.Index); exact (catalog_7.units (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (Bool.true), classId := 0 },
                       { item := (Bool.false), classId := 1 }]
                     nodup := by
                       letI := catalog_7.arena.stateDecidableEq; letI := catalog_7.arena.stateFintype
                       change ([(Bool.true), (Bool.false)] : List (Bool)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_7.arena.stateDecidableEq; letI := catalog_7.arena.stateFintype
                       change ∀ x : (Bool), x ∈ [(Bool.true), (Bool.false)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_7.arena.stateDecidableEq; letI := catalog_7.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

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
      enumeration := {
        states := ([(D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.a), (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.b), (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.c), (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.d)] : List (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_8 : Contract.SealFacts catalog_8 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange.commutativity_hypothesis_is_necessary_realization.toTheoremUnit
           D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 12
        uniqueEq := ((catalog_8.rows (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).uniqueEq).trans (by rfl)
        without := 12
        withoutEq := ((catalog_8.rows (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_8.rows (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_8.rows (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).roleBins = ![0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_8.nondegenerate).mpr
          rw [(catalog_8.rows (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).uniqueEq]
          decide +kernel) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 6, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 8, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 9, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 10, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 11, within := by decide +kernel, item := 6, correct := by decide +kernel },
                  { position := 12, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 13, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 14, within := by decide +kernel, item := 0, correct := by decide +kernel }]
                complete := rfl }
      axes := { rows := [{ index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowF), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.flow, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowG), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.flow, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowF), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowG), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_8.units (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).primitives.Index); exact (catalog_8.units (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_8.units (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).primitives.Index); exact (catalog_8.units (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowF), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowG), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_8.units (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).primitives.Index); exact (catalog_8.units (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_8.units (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).primitives.Index); exact (catalog_8.units (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.a), classId := 0 },
                       { item := (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.b), classId := 1 },
                       { item := (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.c), classId := 2 },
                       { item := (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.d), classId := 3 }]
                     nodup := by
                       letI := catalog_8.arena.stateDecidableEq; letI := catalog_8.arena.stateFintype
                       change ([(D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.a), (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.b), (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.c), (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.d)] : List (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_8.arena.stateDecidableEq; letI := catalog_8.arena.stateFintype
                       change ∀ x : (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState), x ∈ [(D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.a), (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.b), (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.c), (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.d)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_8.arena.stateDecidableEq; letI := catalog_8.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

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
      enumeration := {
        states := ([(state_59), (state_60), (state_61), (state_62), (state_63), (state_64), (state_65), (state_66), (state_67)] : List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
  Option D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_9 : Contract.SealFacts catalog_9 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_realization.toTheoremUnit
           D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 60
        uniqueEq := ((catalog_9.rows (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).uniqueEq).trans (by rfl)
        without := 72
        withoutEq := ((catalog_9.rows (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 12, 0, 0, 0, 0, 30, 0, 0, 18, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_9.rows (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_9.rows (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).roleBins = ![0, 0, 12, 0, 0, 0, 0, 30, 0, 0, 18, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_9.nondegenerate).mpr
          rw [(catalog_9.rows (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).uniqueEq]
          decide +kernel) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 12, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 30, correct := by decide +kernel },
                  { position := 8, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 9, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 10, within := by decide +kernel, item := 18, correct := by decide +kernel },
                  { position := 11, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 12, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 13, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 14, within := by decide +kernel, item := 0, correct := by decide +kernel }]
                complete := rfl }
      axes := { rows := [{ index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutEnd), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutCause), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.admitAThenB), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.admit, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.admitBThenA), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.admit, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inr
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionAnchor.aThenB), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.anchor, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inr
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionAnchor.bThenA), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.anchor, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutEnd), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutCause), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.admitAThenB), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.admitBThenA), (@Sum.inr
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionAnchor.aThenB), (@Sum.inr
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionAnchor.bThenA)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_9.units (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).primitives.Index); exact (catalog_9.units (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_9.units (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).primitives.Index); exact (catalog_9.units (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutEnd), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.cutCause), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.admitAThenB), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionReadout.admitBThenA), (@Sum.inr
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionAnchor.aThenB), (@Sum.inr
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.State
            D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature)
          D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.PreemptionAnchor.bThenA)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_9.units (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).primitives.Index); exact (catalog_9.units (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_9.units (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).primitives.Index); exact (catalog_9.units (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (state_59), classId := 0 },
                       { item := (state_60), classId := 1 },
                       { item := (state_61), classId := 2 },
                       { item := (state_62), classId := 1 },
                       { item := (state_63), classId := 1 },
                       { item := (state_64), classId := 3 },
                       { item := (state_65), classId := 2 },
                       { item := (state_66), classId := 4 },
                       { item := (state_67), classId := 2 }]
                     nodup := by
                       letI := catalog_9.arena.stateDecidableEq; letI := catalog_9.arena.stateFintype
                       change ([(state_59), (state_60), (state_61), (state_62), (state_63), (state_64), (state_65), (state_66), (state_67)] : List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
               Option D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_9.arena.stateDecidableEq; letI := catalog_9.arena.stateFintype
                       change ∀ x : (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
               Option D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism), x ∈ [(state_59), (state_60), (state_61), (state_62), (state_63), (state_64), (state_65), (state_66), (state_67)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_9.arena.stateDecidableEq; letI := catalog_9.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

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
      enumeration := {
        states := ([(D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t1), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t2), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t3), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t4), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t5)] : List (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

end Reg.Catalogs.InformationRoot.SealedCatalog
