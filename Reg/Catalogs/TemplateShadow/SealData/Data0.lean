import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Tactic.FinCases
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.Aggregation.AgendaPower
import D5.S3.ConceptDynamics.CIRPT.PrimitiveKernel
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Fused
import D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
import D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
import Reg.Catalogs.TemplateShadow.SealData.States0
import Reg.Support.LegacyAgenda
import Reg.Support.LegacyCausalCoordinates
import Reg.Support.LegacyCausalFinite
import Reg.Support.LegacyCausalSlots
import Reg.Support.LegacyContextReplacement
import Reg.Support.LegacyFiniteTransport

namespace Reg.Catalogs.TemplateShadow.SealedCatalog
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
      enumeration := {
        states := ([(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15), (state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (state_26)] : List (Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three)))
        nodup := by letI := ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_0 : Contract.SealFacts catalog_0 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyAgenda.bridge.toTheoremUnit D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 570
        uniqueEq := ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq).trans (by rfl)
        without := 702
        withoutEq := ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 84, 0, 0, 0, 0, 0, 318, 0, 168, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).roleBins = ![0, 84, 0, 0, 0, 0, 0, 318, 0, 168, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_0.nondegenerate).mpr
          rw [(catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq]
          decide +kernel) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 84, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 318, correct := by decide +kernel },
                  { position := 8, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 9, within := by decide +kernel, item := 168, correct := by decide +kernel },
                  { position := 10, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 11, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 12, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 13, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 14, within := by decide +kernel, item := 0, correct := by decide +kernel }]
                complete := rfl }
      axes := { rows := [{ index := by change Sum _ _; exact (@Sum.inl
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyAgenda.arena.State
                 (@Reg.Support.LegacyFiniteTransport.agendaSignature Reg.Support.LegacyAgenda.State
                   (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                   (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyAgenda.arena.State
                 (@Reg.Support.LegacyFiniteTransport.agendaSignature Reg.Support.LegacyAgenda.State
                   (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                   (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
               Bool.true), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.admit, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyAgenda.arena.State
            (@Reg.Support.LegacyFiniteTransport.agendaSignature Reg.Support.LegacyAgenda.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyAgenda.arena.State
            (@Reg.Support.LegacyFiniteTransport.agendaSignature Reg.Support.LegacyAgenda.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          Bool.false), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyAgenda.arena.State
            (@Reg.Support.LegacyFiniteTransport.agendaSignature Reg.Support.LegacyAgenda.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyAgenda.arena.State
            (@Reg.Support.LegacyFiniteTransport.agendaSignature Reg.Support.LegacyAgenda.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyAgenda.arena.State
            (@Reg.Support.LegacyFiniteTransport.agendaSignature Reg.Support.LegacyAgenda.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyAgenda.arena.State
            (@Reg.Support.LegacyFiniteTransport.agendaSignature Reg.Support.LegacyAgenda.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          Bool.false)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyAgenda.arena.State
            (@Reg.Support.LegacyFiniteTransport.agendaSignature Reg.Support.LegacyAgenda.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyAgenda.arena.State
            (@Reg.Support.LegacyFiniteTransport.agendaSignature Reg.Support.LegacyAgenda.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyAgenda.arena.State
            (@Reg.Support.LegacyFiniteTransport.agendaSignature Reg.Support.LegacyAgenda.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyAgenda.arena.State
            (@Reg.Support.LegacyFiniteTransport.agendaSignature Reg.Support.LegacyAgenda.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyAgenda.arena.State
            (@Reg.Support.LegacyFiniteTransport.agendaSignature Reg.Support.LegacyAgenda.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyAgenda.arena.State
            (@Reg.Support.LegacyFiniteTransport.agendaSignature Reg.Support.LegacyAgenda.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyAgenda.arena.State
            (@Reg.Support.LegacyFiniteTransport.agendaSignature Reg.Support.LegacyAgenda.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyAgenda.arena.State
            (@Reg.Support.LegacyFiniteTransport.agendaSignature Reg.Support.LegacyAgenda.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          Bool.false)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (state_0), classId := 0 },
                       { item := (state_1), classId := 0 },
                       { item := (state_2), classId := 1 },
                       { item := (state_3), classId := 0 },
                       { item := (state_4), classId := 0 },
                       { item := (state_5), classId := 0 },
                       { item := (state_6), classId := 1 },
                       { item := (state_7), classId := 0 },
                       { item := (state_8), classId := 0 },
                       { item := (state_9), classId := 2 },
                       { item := (state_10), classId := 2 },
                       { item := (state_11), classId := 3 },
                       { item := (state_12), classId := 2 },
                       { item := (state_13), classId := 2 },
                       { item := (state_14), classId := 2 },
                       { item := (state_15), classId := 3 },
                       { item := (state_16), classId := 2 },
                       { item := (state_17), classId := 2 },
                       { item := (state_18), classId := 4 },
                       { item := (state_19), classId := 4 },
                       { item := (state_20), classId := 5 },
                       { item := (state_21), classId := 4 },
                       { item := (state_22), classId := 4 },
                       { item := (state_23), classId := 4 },
                       { item := (state_24), classId := 5 },
                       { item := (state_25), classId := 4 },
                       { item := (state_26), classId := 4 }]
                     nodup := by
                       letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype
                       change ([(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15), (state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (state_26)] : List (Prod Reg.Support.LegacyFiniteTransport.Three
               (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three))).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype
                       change ∀ x : (Prod Reg.Support.LegacyFiniteTransport.Three
               (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three)), x ∈ [(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15), (state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (state_26)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

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
      enumeration := {
        states := ([(@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
  (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
  (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
  (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
  (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
  (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
  (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
  (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
  (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
  (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
  (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
  (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
  (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
  (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
  (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
  (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
  (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)))] : List (Prod Bool (Prod Bool (Prod Bool Bool))))
        nodup := by letI := ((_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena)).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena)).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena)).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena)).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_1 : Contract.SealFacts catalog_1 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyCausalFinite.local_bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 240
        uniqueEq := ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).uniqueEq).trans (by rfl)
        without := 240
        withoutEq := ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_1.nondegenerate).mpr
          rw [(catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).uniqueEq]
          decide +kernel) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 240, correct := by decide +kernel },
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
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 0)
            (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                          (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 1)
            (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 2)
            (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 3)
            (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 4)
            (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 5)
            (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 6)
            (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 7)
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 0)
            (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                          (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 1)
            (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 2)
            (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 3)
            (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 4)
            (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 5)
            (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 6)
            (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 7)
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool)))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 0)
            (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                          (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 1)
            (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 2)
            (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 3)
            (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 4)
            (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 5)
            (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 6)
            (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.icObjectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.ICData Bool instDecidableEqBool))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 7)
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true))), classId := 0 },
                       { item := (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false))), classId := 1 },
                       { item := (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true))), classId := 2 },
                       { item := (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false))), classId := 3 },
                       { item := (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true))), classId := 4 },
                       { item := (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false))), classId := 5 },
                       { item := (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true))), classId := 6 },
                       { item := (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false))), classId := 7 },
                       { item := (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true))), classId := 8 },
                       { item := (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false))), classId := 9 },
                       { item := (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true))), classId := 10 },
                       { item := (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false))), classId := 11 },
                       { item := (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true))), classId := 12 },
                       { item := (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false))), classId := 13 },
                       { item := (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true))), classId := 14 },
                       { item := (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false))), classId := 15 }]
                     nodup := by
                       letI := catalog_1.arena.stateDecidableEq; letI := catalog_1.arena.stateFintype
                       change ([(@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)))] : List (Prod Bool (Prod Bool (Prod Bool Bool)))).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_1.arena.stateDecidableEq; letI := catalog_1.arena.stateFintype
                       change ∀ x : (Prod Bool (Prod Bool (Prod Bool Bool))), x ∈ [(@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true))), (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
               (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)))]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_1.arena.stateDecidableEq; letI := catalog_1.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

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
      enumeration := {
        states := ([(@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false))] : List (Prod Bool (Prod Bool Bool)))
        nodup := by letI := ((_root_.Reg.Support.LegacyContextReplacement.objectArena)).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyContextReplacement.objectArena)).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.Reg.Support.LegacyContextReplacement.objectArena)).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyContextReplacement.objectArena)).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

end Reg.Catalogs.TemplateShadow.SealedCatalog
