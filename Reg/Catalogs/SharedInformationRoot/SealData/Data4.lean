import Mathlib.Data.Fin.VecNotation
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.CIRPT.PrimitiveKernel
import D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
import D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.SystemUnit
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange
import D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
import D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
import D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
import Reg.Catalogs.InformationRoot.SealedCatalog
import Reg.Catalogs.SharedInformationRoot.SealData.States10
import Reg.Catalogs.SharedInformationRoot.SealData.States11
import Reg.Catalogs.SharedInformationRoot.SealData.States12
import Reg.Catalogs.SharedInformationRoot.SealData.States13
import Reg.Catalogs.SharedInformationRoot.SealData.States14
import Reg.Catalogs.SharedInformationRoot.SealData.States15
import Reg.Catalogs.SharedInformationRoot.SealData.States16
import Reg.Catalogs.SharedInformationRoot.SealData.States17
import Reg.Catalogs.SharedInformationRoot.SealData.States9
import Reg.Support.LegacySpectrum

set_option backward.isDefEq.respectTransparency.types false

namespace Reg.Catalogs.SharedInformationRoot.SealedCatalog
open LeanInformationAudit

noncomputable def catalog_8 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.SystemUnit.systemRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[7]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[7]'(by decide))).catalog.bundleNonempty
      stateCard := 2
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[7]'(by decide))).catalog.stateCardEq
      full := 0
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[7]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[7]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[7]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := {
        states := ([(Bool.true), (Bool.false)] : List (Bool))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_8 : Contract.SealFacts catalog_8 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.SystemUnit.system_self_application_realization.toTheoremUnit
           D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 2
        uniqueEq := ((catalog_8.rows (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).uniqueEq).trans (by rfl)
        without := 2
        withoutEq := ((catalog_8.rows (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_8.rows (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_8.rows (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_8.nondegenerate).mpr
          rw [(catalog_8.rows (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).uniqueEq]
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_8.units (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).primitives.Index); exact (catalog_8.units (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_8.units (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).primitives.Index); exact (catalog_8.units (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).primitives.indexFintype)
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_8.units (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).primitives.Index); exact (catalog_8.units (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_8.units (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).primitives.Index); exact (catalog_8.units (⟨0, by decide +kernel⟩ : Fin catalog_8.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (Bool.true), classId := 0 },
                       { item := (Bool.false), classId := 1 }]
                     nodup := by
                       letI := catalog_8.arena.stateDecidableEq; letI := catalog_8.arena.stateFintype
                       change ([(Bool.true), (Bool.false)] : List (Bool)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_8.arena.stateDecidableEq; letI := catalog_8.arena.stateFintype
                       change ∀ x : (Bool), x ∈ [(Bool.true), (Bool.false)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_8.arena.stateDecidableEq; letI := catalog_8.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

noncomputable def catalog_9 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange.commutingCompletionRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[8]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[8]'(by decide))).catalog.bundleNonempty
      stateCard := 4
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[8]'(by decide))).catalog.stateCardEq
      full := 0
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[8]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[8]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[8]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := {
        states := ([(D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.a), (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.b), (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.c), (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.d)] : List (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_9 : Contract.SealFacts catalog_9 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange.commutativity_hypothesis_is_necessary_realization.toTheoremUnit
           D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 12
        uniqueEq := ((catalog_9.rows (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).uniqueEq).trans (by rfl)
        without := 12
        withoutEq := ((catalog_9.rows (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_9.rows (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_9.rows (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).roleBins = ![0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_9.nondegenerate).mpr
          rw [(catalog_9.rows (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).uniqueEq]
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_9.units (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).primitives.Index); exact (catalog_9.units (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_9.units (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).primitives.Index); exact (catalog_9.units (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).primitives.indexFintype)
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_9.units (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).primitives.Index); exact (catalog_9.units (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_9.units (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).primitives.Index); exact (catalog_9.units (⟨0, by decide +kernel⟩ : Fin catalog_9.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.a), classId := 0 },
                       { item := (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.b), classId := 1 },
                       { item := (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.c), classId := 2 },
                       { item := (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.d), classId := 3 }]
                     nodup := by
                       letI := catalog_9.arena.stateDecidableEq; letI := catalog_9.arena.stateFintype
                       change ([(D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.a), (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.b), (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.c), (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.d)] : List (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_9.arena.stateDecidableEq; letI := catalog_9.arena.stateFintype
                       change ∀ x : (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState), x ∈ [(D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.a), (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.b), (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.c), (D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState.d)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_9.arena.stateDecidableEq; letI := catalog_9.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

noncomputable def catalog_10 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[9]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[9]'(by decide))).catalog.bundleNonempty
      stateCard := 9
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[9]'(by decide))).catalog.stateCardEq
      full := 12
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[9]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[9]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[9]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := {
        states := ([(state_91), (state_92), (state_93), (state_94), (state_95), (state_96), (state_97), (state_98), (state_99)] : List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
  Option D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_10 : Contract.SealFacts catalog_10 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_realization.toTheoremUnit
           D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 60
        uniqueEq := ((catalog_10.rows (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).uniqueEq).trans (by rfl)
        without := 72
        withoutEq := ((catalog_10.rows (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 12, 0, 0, 0, 0, 30, 0, 0, 18, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_10.rows (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_10.rows (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).roleBins = ![0, 0, 12, 0, 0, 0, 0, 30, 0, 0, 18, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_10.nondegenerate).mpr
          rw [(catalog_10.rows (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).uniqueEq]
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_10.units (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).primitives.Index); exact (catalog_10.units (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_10.units (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).primitives.Index); exact (catalog_10.units (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).primitives.indexFintype)
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_10.units (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).primitives.Index); exact (catalog_10.units (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_10.units (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).primitives.Index); exact (catalog_10.units (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (state_91), classId := 0 },
                       { item := (state_92), classId := 1 },
                       { item := (state_93), classId := 2 },
                       { item := (state_94), classId := 1 },
                       { item := (state_95), classId := 1 },
                       { item := (state_96), classId := 3 },
                       { item := (state_97), classId := 2 },
                       { item := (state_98), classId := 4 },
                       { item := (state_99), classId := 2 }]
                     nodup := by
                       letI := catalog_10.arena.stateDecidableEq; letI := catalog_10.arena.stateFintype
                       change ([(state_91), (state_92), (state_93), (state_94), (state_95), (state_96), (state_97), (state_98), (state_99)] : List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
               Option D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_10.arena.stateDecidableEq; letI := catalog_10.arena.stateFintype
                       change ∀ x : (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
               Option D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism), x ∈ [(state_91), (state_92), (state_93), (state_94), (state_95), (state_96), (state_97), (state_98), (state_99)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_10.arena.stateDecidableEq; letI := catalog_10.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

noncomputable def catalog_11 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena).toArena).stateDecidableEq (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutRealization D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) fun (atom : D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom) => Reg.Support.LegacySpectrum.indexReadout atom)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[10]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[10]'(by decide))).catalog.bundleNonempty
      stateCard := 5
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[10]'(by decide))).catalog.stateCardEq
      full := 0
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[10]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[10]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[10]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := {
        states := ([(D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t1), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t2), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t3), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t4), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t5)] : List (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_11 : Contract.SealFacts catalog_11 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacySpectrum.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 20
        uniqueEq := ((catalog_11.rows (⟨0, by decide +kernel⟩ : Fin catalog_11.size)).uniqueEq).trans (by rfl)
        without := 20
        withoutEq := ((catalog_11.rows (⟨0, by decide +kernel⟩ : Fin catalog_11.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_11.rows (⟨0, by decide +kernel⟩ : Fin catalog_11.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_11.rows (⟨0, by decide +kernel⟩ : Fin catalog_11.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_11.nondegenerate).mpr
          rw [(catalog_11.rows (⟨0, by decide +kernel⟩ : Fin catalog_11.size)).uniqueEq]
          decide +kernel) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 20, correct := by decide +kernel },
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
                D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
                (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
                  D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
                  (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
              (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
                (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
                  D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
                  (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
              PUnit.unit), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          PUnit.unit)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_11.units (⟨0, by decide +kernel⟩ : Fin catalog_11.size)).primitives.Index); exact (catalog_11.units (⟨0, by decide +kernel⟩ : Fin catalog_11.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_11.units (⟨0, by decide +kernel⟩ : Fin catalog_11.size)).primitives.Index); exact (catalog_11.units (⟨0, by decide +kernel⟩ : Fin catalog_11.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          PUnit.unit)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_11.units (⟨0, by decide +kernel⟩ : Fin catalog_11.size)).primitives.Index); exact (catalog_11.units (⟨0, by decide +kernel⟩ : Fin catalog_11.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_11.units (⟨0, by decide +kernel⟩ : Fin catalog_11.size)).primitives.Index); exact (catalog_11.units (⟨0, by decide +kernel⟩ : Fin catalog_11.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t1), classId := 0 },
                       { item := (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t2), classId := 1 },
                       { item := (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t3), classId := 2 },
                       { item := (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t4), classId := 3 },
                       { item := (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t5), classId := 4 }]
                     nodup := by
                       letI := catalog_11.arena.stateDecidableEq; letI := catalog_11.arena.stateFintype
                       change ([(D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t1), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t2), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t3), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t4), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t5)] : List (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_11.arena.stateDecidableEq; letI := catalog_11.arena.stateFintype
                       change ∀ x : (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom), x ∈ [(D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t1), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t2), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t3), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t4), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t5)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_11.arena.stateDecidableEq; letI := catalog_11.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

end Reg.Catalogs.SharedInformationRoot.SealedCatalog
