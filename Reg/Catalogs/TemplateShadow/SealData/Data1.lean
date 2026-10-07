import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Tactic.FinCases
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.CIRPT.PrimitiveKernel
import D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
import D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign
import D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Fused
import D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
import D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
import Reg.Catalogs.TemplateShadow.SealData.Data0
import Reg.Catalogs.TemplateShadow.SealData.States0
import Reg.Catalogs.TemplateShadow.SealData.States1
import Reg.Catalogs.TemplateShadow.SealData.States2
import Reg.Catalogs.TemplateShadow.SealData.States3
import Reg.Catalogs.TemplateShadow.SealData.States4
import Reg.Catalogs.TemplateShadow.SealData.States5
import Reg.Catalogs.TemplateShadow.SealData.States6
import Reg.Catalogs.TemplateShadow.SealData.States7
import Reg.Catalogs.TemplateShadow.SealData.States8
import Reg.Support.LegacyContextReplacement
import Reg.Support.LegacyFiniteTransport
import Reg.Support.LegacyGluing
import Reg.Support.LegacyResidue
import Reg.Support.LegacyStaticDesign

namespace Reg.Catalogs.TemplateShadow.SealedCatalog
open LeanInformationAudit

noncomputable def facts_2 : Contract.SealFacts catalog_2 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyContextReplacement.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 56
        uniqueEq := ((catalog_2.rows (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).uniqueEq).trans (by rfl)
        without := 56
        withoutEq := ((catalog_2.rows (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_2.rows (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_2.rows (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_2.nondegenerate).mpr
          rw [(catalog_2.rows (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).uniqueEq]
          decide +kernel) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 56, correct := by decide +kernel },
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
                Reg.Support.LegacyContextReplacement.objectArena.State
                (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
                  Reg.Support.LegacyContextReplacement.ContextData (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
              (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                Reg.Support.LegacyContextReplacement.objectArena.State
                (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
                  Reg.Support.LegacyContextReplacement.ContextData (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
              PUnit.unit), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyContextReplacement.objectArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              Reg.Support.LegacyContextReplacement.ContextData (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyContextReplacement.objectArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              Reg.Support.LegacyContextReplacement.ContextData (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
          PUnit.unit)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyContextReplacement.objectArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              Reg.Support.LegacyContextReplacement.ContextData (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyContextReplacement.objectArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              Reg.Support.LegacyContextReplacement.ContextData (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.Index); exact (catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.Index); exact (catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyContextReplacement.objectArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              Reg.Support.LegacyContextReplacement.ContextData (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyContextReplacement.objectArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              Reg.Support.LegacyContextReplacement.ContextData (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyContextReplacement.objectArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              Reg.Support.LegacyContextReplacement.ContextData (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyContextReplacement.objectArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              Reg.Support.LegacyContextReplacement.ContextData (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
          PUnit.unit)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.Index); exact (catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.Index); exact (catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)), classId := 0 },
                       { item := (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)), classId := 1 },
                       { item := (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)), classId := 2 },
                       { item := (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)), classId := 3 },
                       { item := (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)), classId := 4 },
                       { item := (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)), classId := 5 },
                       { item := (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)), classId := 6 },
                       { item := (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)), classId := 7 }]
                     nodup := by
                       letI := catalog_2.arena.stateDecidableEq; letI := catalog_2.arena.stateFintype
                       change ([(@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false))] : List (Prod Bool (Prod Bool Bool))).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_2.arena.stateDecidableEq; letI := catalog_2.arena.stateFintype
                       change ∀ x : (Prod Bool (Prod Bool Bool)), x ∈ [(@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false))]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_2.arena.stateDecidableEq; letI := catalog_2.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

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
      enumeration := {
        states := ([(@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false))] : List (Prod Bool (Prod Bool Bool)))
        nodup := by letI := ((_root_.Reg.Support.LegacyGluing.arena).toArena).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyGluing.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.Reg.Support.LegacyGluing.arena).toArena).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyGluing.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_3 : Contract.SealFacts catalog_3 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyGluing.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 48
        uniqueEq := ((catalog_3.rows (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).uniqueEq).trans (by rfl)
        without := 56
        withoutEq := ((catalog_3.rows (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_3.rows (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_3.rows (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).roleBins = ![0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_3.nondegenerate).mpr
          rw [(catalog_3.rows (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).uniqueEq]
          decide +kernel) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 48, correct := by decide +kernel },
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
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 0)
            (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.admit, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 1)
            (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.admit, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 2)
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.admit, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 0)
            (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 1)
            (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 2)
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_3.units (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).primitives.Index); exact (catalog_3.units (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_3.units (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).primitives.Index); exact (catalog_3.units (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 0)
            (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 1)
            (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyGluing.arena.State
            (@Reg.Support.LegacyFiniteTransport.admitSignature Reg.Support.LegacyGluing.State
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 2)
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_3.units (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).primitives.Index); exact (catalog_3.units (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_3.units (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).primitives.Index); exact (catalog_3.units (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)), classId := 0 },
                       { item := (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)), classId := 1 },
                       { item := (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)), classId := 2 },
                       { item := (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)), classId := 3 },
                       { item := (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)), classId := 3 },
                       { item := (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)), classId := 2 },
                       { item := (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)), classId := 1 },
                       { item := (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)), classId := 0 }]
                     nodup := by
                       letI := catalog_3.arena.stateDecidableEq; letI := catalog_3.arena.stateFintype
                       change ([(@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false))] : List (Prod Bool (Prod Bool Bool))).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_3.arena.stateDecidableEq; letI := catalog_3.arena.stateFintype
                       change ∀ x : (Prod Bool (Prod Bool Bool)), x ∈ [(@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false))]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_3.arena.stateDecidableEq; letI := catalog_3.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

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
      enumeration := {
        states := ([(@Prod.mk Bool Bool Bool.true Bool.true), (@Prod.mk Bool Bool Bool.true Bool.false), (@Prod.mk Bool Bool Bool.false Bool.true), (@Prod.mk Bool Bool Bool.false Bool.false)] : List (Prod Bool Bool))
        nodup := by letI := ((_root_.Reg.Support.LegacyResidue.arena).toArena).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyResidue.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.Reg.Support.LegacyResidue.arena).toArena).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyResidue.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_4 : Contract.SealFacts catalog_4 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyResidue.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 12
        uniqueEq := ((catalog_4.rows (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).uniqueEq).trans (by rfl)
        without := 12
        withoutEq := ((catalog_4.rows (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_4.rows (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_4.rows (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_4.nondegenerate).mpr
          rw [(catalog_4.rows (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).uniqueEq]
          decide +kernel) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 12, correct := by decide +kernel },
                  { position := 8, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 9, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 10, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 11, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 12, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 13, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 14, within := by decide +kernel, item := 0, correct := by decide +kernel }]
                complete := rfl }
      axes := { rows := [{ index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 0)
            (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 1)
            (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 2)
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 0)
            (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 1)
            (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 2)
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_4.units (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).primitives.Index); exact (catalog_4.units (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_4.units (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).primitives.Index); exact (catalog_4.units (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 0)
            (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 1)
            (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyResidue.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyResidue.State (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 2)
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_4.units (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).primitives.Index); exact (catalog_4.units (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_4.units (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).primitives.Index); exact (catalog_4.units (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (@Prod.mk Bool Bool Bool.true Bool.true), classId := 0 },
                       { item := (@Prod.mk Bool Bool Bool.true Bool.false), classId := 1 },
                       { item := (@Prod.mk Bool Bool Bool.false Bool.true), classId := 2 },
                       { item := (@Prod.mk Bool Bool Bool.false Bool.false), classId := 3 }]
                     nodup := by
                       letI := catalog_4.arena.stateDecidableEq; letI := catalog_4.arena.stateFintype
                       change ([(@Prod.mk Bool Bool Bool.true Bool.true), (@Prod.mk Bool Bool Bool.true Bool.false), (@Prod.mk Bool Bool Bool.false Bool.true), (@Prod.mk Bool Bool Bool.false Bool.false)] : List (Prod Bool Bool)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_4.arena.stateDecidableEq; letI := catalog_4.arena.stateFintype
                       change ∀ x : (Prod Bool Bool), x ∈ [(@Prod.mk Bool Bool Bool.true Bool.true), (@Prod.mk Bool Bool Bool.true Bool.false), (@Prod.mk Bool Bool Bool.false Bool.true), (@Prod.mk Bool Bool Bool.false Bool.false)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_4.arena.stateDecidableEq; letI := catalog_4.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

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
      enumeration := {
        states := ([(@Sum.inl Bool Unit Bool.true), (@Sum.inl Bool Unit Bool.false), (@Sum.inr Bool Unit PUnit.unit)] : List (Sum Bool Unit))
        nodup := by letI := ((_root_.Reg.Support.LegacyStaticDesign.arena).toArena).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyStaticDesign.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.Reg.Support.LegacyStaticDesign.arena).toArena).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyStaticDesign.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_5 : Contract.SealFacts catalog_5 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyStaticDesign.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 6
        uniqueEq := ((catalog_5.rows (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).uniqueEq).trans (by rfl)
        without := 6
        withoutEq := ((catalog_5.rows (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_5.rows (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_5.rows (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_5.nondegenerate).mpr
          rw [(catalog_5.rows (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).uniqueEq]
          decide +kernel) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 6, correct := by decide +kernel },
                  { position := 8, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 9, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 10, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 11, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 12, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 13, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 14, within := by decide +kernel, item := 0, correct := by decide +kernel }]
                complete := rfl }
      axes := { rows := [{ index := by change Sum _ _; exact (@Sum.inl
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyStaticDesign.arena.State
                 (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
                   Reg.Support.LegacyFiniteTransport.Three Bool Bool.fintype instDecidableEqBool))
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyStaticDesign.arena.State
                 (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
                   Reg.Support.LegacyFiniteTransport.Three Bool Bool.fintype instDecidableEqBool))
               Bool.true), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyStaticDesign.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyFiniteTransport.Three Bool Bool.fintype instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyStaticDesign.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyFiniteTransport.Three Bool Bool.fintype instDecidableEqBool))
          Bool.false), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyStaticDesign.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyFiniteTransport.Three Bool Bool.fintype instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyStaticDesign.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyFiniteTransport.Three Bool Bool.fintype instDecidableEqBool))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyStaticDesign.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyFiniteTransport.Three Bool Bool.fintype instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyStaticDesign.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyFiniteTransport.Three Bool Bool.fintype instDecidableEqBool))
          Bool.false)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyStaticDesign.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyFiniteTransport.Three Bool Bool.fintype instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyStaticDesign.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyFiniteTransport.Three Bool Bool.fintype instDecidableEqBool)))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_5.units (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).primitives.Index); exact (catalog_5.units (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_5.units (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).primitives.Index); exact (catalog_5.units (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyStaticDesign.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyFiniteTransport.Three Bool Bool.fintype instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyStaticDesign.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyFiniteTransport.Three Bool Bool.fintype instDecidableEqBool))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyStaticDesign.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyFiniteTransport.Three Bool Bool.fintype instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyStaticDesign.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyFiniteTransport.Three Bool Bool.fintype instDecidableEqBool))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index Reg.Support.LegacyStaticDesign.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyFiniteTransport.Three Bool Bool.fintype instDecidableEqBool))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex Reg.Support.LegacyStaticDesign.arena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilySignature
              Reg.Support.LegacyFiniteTransport.Three Bool Bool.fintype instDecidableEqBool))
          Bool.false)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_5.units (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).primitives.Index); exact (catalog_5.units (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_5.units (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).primitives.Index); exact (catalog_5.units (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (@Sum.inl Bool Unit Bool.true), classId := 0 },
                       { item := (@Sum.inl Bool Unit Bool.false), classId := 1 },
                       { item := (@Sum.inr Bool Unit PUnit.unit), classId := 2 }]
                     nodup := by
                       letI := catalog_5.arena.stateDecidableEq; letI := catalog_5.arena.stateFintype
                       change ([(@Sum.inl Bool Unit Bool.true), (@Sum.inl Bool Unit Bool.false), (@Sum.inr Bool Unit PUnit.unit)] : List (Sum Bool Unit)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_5.arena.stateDecidableEq; letI := catalog_5.arena.stateFintype
                       change ∀ x : (Sum Bool Unit), x ∈ [(@Sum.inl Bool Unit Bool.true), (@Sum.inl Bool Unit Bool.false), (@Sum.inr Bool Unit PUnit.unit)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_5.arena.stateDecidableEq; letI := catalog_5.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

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
      enumeration := {
        states := ([(state_27), (state_28), (state_29), (state_30), (state_31), (state_32), (state_33), (state_34), (state_35), (state_36), (state_37), (state_38), (state_39), (state_40), (state_41), (state_42), (state_43), (state_44), (state_45), (state_46), (state_47), (state_48), (state_49), (state_50), (state_51), (state_52), (state_53), (state_54), (state_55), (state_56), (state_57), (state_58)] : List (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
        nodup := by letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateFintype; change ([(state_27), (state_28), (state_29), (state_30), (state_31), (state_32), (state_33), (state_34), (state_35), (state_36), (state_37), (state_38), (state_39), (state_40), (state_41), (state_42), (state_43), (state_44), (state_45), (state_46), (state_47), (state_48), (state_49), (state_50), (state_51), (state_52), (state_53), (state_54), (state_55), (state_56), (state_57), (state_58)] : List (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)).Nodup; apply of_decide_eq_true; decide +kernel
        complete := by letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateFintype; change ([(state_27), (state_28), (state_29), (state_30), (state_31), (state_32), (state_33), (state_34), (state_35), (state_36), (state_37), (state_38), (state_39), (state_40), (state_41), (state_42), (state_43), (state_44), (state_45), (state_46), (state_47), (state_48), (state_49), (state_50), (state_51), (state_52), (state_53), (state_54), (state_55), (state_56), (state_57), (state_58)] : List (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)).toFinset = (Finset.univ : Finset (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)); apply of_decide_eq_true; decide +kernel }
    }

end Reg.Catalogs.TemplateShadow.SealedCatalog
