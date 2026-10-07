import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.CIRPT.PrimitiveKernel
import D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
import D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign
import D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
import Reg.Catalogs.InformationRoot.SealedCatalog
import Reg.Catalogs.SharedInformationRoot.SealData.Data2
import Reg.Catalogs.SharedInformationRoot.SealData.States0
import Reg.Catalogs.SharedInformationRoot.SealData.States1
import Reg.Catalogs.SharedInformationRoot.SealData.States2
import Reg.Catalogs.SharedInformationRoot.SealData.States3
import Reg.Catalogs.SharedInformationRoot.SealData.States4
import Reg.Catalogs.SharedInformationRoot.SealData.States5
import Reg.Catalogs.SharedInformationRoot.SealData.States6
import Reg.Catalogs.SharedInformationRoot.SealData.States7
import Reg.Catalogs.SharedInformationRoot.SealData.States8
import Reg.Support.LegacyFiniteTransport
import Reg.Support.LegacyGluing
import Reg.Support.LegacyResidue
import Reg.Support.LegacyStaticDesign

set_option backward.isDefEq.respectTransparency.types false

namespace Reg.Catalogs.SharedInformationRoot.SealedCatalog
open LeanInformationAudit

noncomputable def facts_4 : Contract.SealFacts catalog_4 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyGluing.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 48
        uniqueEq := ((catalog_4.rows (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).uniqueEq).trans (by rfl)
        without := 56
        withoutEq := ((catalog_4.rows (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_4.rows (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_4.rows (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).roleBins = ![0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_4.nondegenerate).mpr
          rw [(catalog_4.rows (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).uniqueEq]
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_4.units (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).primitives.Index); exact (catalog_4.units (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_4.units (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).primitives.Index); exact (catalog_4.units (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).primitives.indexFintype)
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_4.units (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).primitives.Index); exact (catalog_4.units (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_4.units (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).primitives.Index); exact (catalog_4.units (⟨0, by decide +kernel⟩ : Fin catalog_4.size)).primitives.indexFintype)
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
                       letI := catalog_4.arena.stateDecidableEq; letI := catalog_4.arena.stateFintype
                       change ([(@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false))] : List (Prod Bool (Prod Bool Bool))).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_4.arena.stateDecidableEq; letI := catalog_4.arena.stateFintype
                       change ∀ x : (Prod Bool (Prod Bool Bool)), x ∈ [(@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false))]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_4.arena.stateDecidableEq; letI := catalog_4.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

noncomputable def catalog_5 : Contract.SealCatalog := {
      arenaName := `Reg.Support.LegacyResidue.arena
      catalogId := `Reg.Support.LegacyResidue.arena
      arena := (_root_.Reg.Support.LegacyResidue.arena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyResidue.arena).toArena).stateDecidableEq (Reg.Support.LegacyResidue.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[4]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[4]'(by decide))).catalog.bundleNonempty
      stateCard := 4
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[4]'(by decide))).catalog.stateCardEq
      full := 0
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[4]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[4]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[4]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := {
        states := ([(@Prod.mk Bool Bool Bool.true Bool.true), (@Prod.mk Bool Bool Bool.true Bool.false), (@Prod.mk Bool Bool Bool.false Bool.true), (@Prod.mk Bool Bool Bool.false Bool.false)] : List (Prod Bool Bool))
        nodup := by letI := ((_root_.Reg.Support.LegacyResidue.arena).toArena).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyResidue.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.Reg.Support.LegacyResidue.arena).toArena).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyResidue.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_5 : Contract.SealFacts catalog_5 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyResidue.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 12
        uniqueEq := ((catalog_5.rows (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).uniqueEq).trans (by rfl)
        without := 12
        withoutEq := ((catalog_5.rows (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_5.rows (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_5.rows (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0]) bucket)
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_5.units (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).primitives.Index); exact (catalog_5.units (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_5.units (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).primitives.Index); exact (catalog_5.units (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).primitives.indexFintype)
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_5.units (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).primitives.Index); exact (catalog_5.units (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_5.units (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).primitives.Index); exact (catalog_5.units (⟨0, by decide +kernel⟩ : Fin catalog_5.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (@Prod.mk Bool Bool Bool.true Bool.true), classId := 0 },
                       { item := (@Prod.mk Bool Bool Bool.true Bool.false), classId := 1 },
                       { item := (@Prod.mk Bool Bool Bool.false Bool.true), classId := 2 },
                       { item := (@Prod.mk Bool Bool Bool.false Bool.false), classId := 3 }]
                     nodup := by
                       letI := catalog_5.arena.stateDecidableEq; letI := catalog_5.arena.stateFintype
                       change ([(@Prod.mk Bool Bool Bool.true Bool.true), (@Prod.mk Bool Bool Bool.true Bool.false), (@Prod.mk Bool Bool Bool.false Bool.true), (@Prod.mk Bool Bool Bool.false Bool.false)] : List (Prod Bool Bool)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_5.arena.stateDecidableEq; letI := catalog_5.arena.stateFintype
                       change ∀ x : (Prod Bool Bool), x ∈ [(@Prod.mk Bool Bool Bool.true Bool.true), (@Prod.mk Bool Bool Bool.true Bool.false), (@Prod.mk Bool Bool Bool.false Bool.true), (@Prod.mk Bool Bool Bool.false Bool.false)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_5.arena.stateDecidableEq; letI := catalog_5.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

noncomputable def catalog_6 : Contract.SealCatalog := {
      arenaName := `Reg.Support.LegacyStaticDesign.arena
      catalogId := `Reg.Support.LegacyStaticDesign.arena
      arena := (_root_.Reg.Support.LegacyStaticDesign.arena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyStaticDesign.arena).toArena).stateDecidableEq (Reg.Support.LegacyStaticDesign.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[5]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[5]'(by decide))).catalog.bundleNonempty
      stateCard := 3
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[5]'(by decide))).catalog.stateCardEq
      full := 0
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[5]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[5]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[5]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := {
        states := ([(@Sum.inl Bool Unit Bool.true), (@Sum.inl Bool Unit Bool.false), (@Sum.inr Bool Unit PUnit.unit)] : List (Sum Bool Unit))
        nodup := by letI := ((_root_.Reg.Support.LegacyStaticDesign.arena).toArena).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyStaticDesign.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.Reg.Support.LegacyStaticDesign.arena).toArena).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyStaticDesign.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_6 : Contract.SealFacts catalog_6 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyStaticDesign.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 6
        uniqueEq := ((catalog_6.rows (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).uniqueEq).trans (by rfl)
        without := 6
        withoutEq := ((catalog_6.rows (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_6.rows (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_6.rows (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0]) bucket)
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_6.units (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).primitives.Index); exact (catalog_6.units (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_6.units (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).primitives.Index); exact (catalog_6.units (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).primitives.indexFintype)
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_6.units (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).primitives.Index); exact (catalog_6.units (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_6.units (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).primitives.Index); exact (catalog_6.units (⟨0, by decide +kernel⟩ : Fin catalog_6.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (@Sum.inl Bool Unit Bool.true), classId := 0 },
                       { item := (@Sum.inl Bool Unit Bool.false), classId := 1 },
                       { item := (@Sum.inr Bool Unit PUnit.unit), classId := 2 }]
                     nodup := by
                       letI := catalog_6.arena.stateDecidableEq; letI := catalog_6.arena.stateFintype
                       change ([(@Sum.inl Bool Unit Bool.true), (@Sum.inl Bool Unit Bool.false), (@Sum.inr Bool Unit PUnit.unit)] : List (Sum Bool Unit)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_6.arena.stateDecidableEq; letI := catalog_6.arena.stateFintype
                       change ∀ x : (Sum Bool Unit), x ∈ [(@Sum.inl Bool Unit Bool.true), (@Sum.inl Bool Unit Bool.false), (@Sum.inr Bool Unit PUnit.unit)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_6.arena.stateDecidableEq; letI := catalog_6.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

noncomputable def catalog_7 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[6]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[6]'(by decide))).catalog.bundleNonempty
      stateCard := 32
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[6]'(by decide))).catalog.stateCardEq
      full := 24
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[6]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[6]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[6]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := {
        states := ([(state_59), (state_60), (state_61), (state_62), (state_63), (state_64), (state_65), (state_66), (state_67), (state_68), (state_69), (state_70), (state_71), (state_72), (state_73), (state_74), (state_75), (state_76), (state_77), (state_78), (state_79), (state_80), (state_81), (state_82), (state_83), (state_84), (state_85), (state_86), (state_87), (state_88), (state_89), (state_90)] : List (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM))
        nodup := by letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateFintype; change ([(state_59), (state_60), (state_61), (state_62), (state_63), (state_64), (state_65), (state_66), (state_67), (state_68), (state_69), (state_70), (state_71), (state_72), (state_73), (state_74), (state_75), (state_76), (state_77), (state_78), (state_79), (state_80), (state_81), (state_82), (state_83), (state_84), (state_85), (state_86), (state_87), (state_88), (state_89), (state_90)] : List (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)).Nodup; apply of_decide_eq_true; decide +kernel
        complete := by letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateFintype; change ([(state_59), (state_60), (state_61), (state_62), (state_63), (state_64), (state_65), (state_66), (state_67), (state_68), (state_69), (state_70), (state_71), (state_72), (state_73), (state_74), (state_75), (state_76), (state_77), (state_78), (state_79), (state_80), (state_81), (state_82), (state_83), (state_84), (state_85), (state_86), (state_87), (state_88), (state_89), (state_90)] : List (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)).toFinset = (Finset.univ : Finset (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)); apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_7 : Contract.SealFacts catalog_7 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 968
        uniqueEq := ((catalog_7.rows (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).uniqueEq).trans (by rfl)
        without := 992
        withoutEq := ((catalog_7.rows (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 968, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_7.rows (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_7.rows (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 968, 0, 0, 0, 0, 0, 0, 0]) bucket)
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_7.units (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).primitives.Index); exact (catalog_7.units (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_7.units (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).primitives.Index); exact (catalog_7.units (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).primitives.indexFintype)
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_7.units (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).primitives.Index); exact (catalog_7.units (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_7.units (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).primitives.Index); exact (catalog_7.units (⟨0, by decide +kernel⟩ : Fin catalog_7.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (state_59), classId := 0 },
                       { item := (state_60), classId := 1 },
                       { item := (state_61), classId := 2 },
                       { item := (state_62), classId := 3 },
                       { item := (state_63), classId := 4 },
                       { item := (state_64), classId := 5 },
                       { item := (state_65), classId := 6 },
                       { item := (state_66), classId := 7 },
                       { item := (state_67), classId := 8 },
                       { item := (state_68), classId := 9 },
                       { item := (state_69), classId := 10 },
                       { item := (state_70), classId := 11 },
                       { item := (state_71), classId := 12 },
                       { item := (state_72), classId := 13 },
                       { item := (state_73), classId := 14 },
                       { item := (state_74), classId := 15 },
                       { item := (state_75), classId := 0 },
                       { item := (state_76), classId := 0 },
                       { item := (state_77), classId := 12 },
                       { item := (state_78), classId := 12 },
                       { item := (state_79), classId := 16 },
                       { item := (state_80), classId := 17 },
                       { item := (state_81), classId := 18 },
                       { item := (state_82), classId := 19 },
                       { item := (state_83), classId := 20 },
                       { item := (state_84), classId := 21 },
                       { item := (state_85), classId := 22 },
                       { item := (state_86), classId := 23 },
                       { item := (state_87), classId := 3 },
                       { item := (state_88), classId := 15 },
                       { item := (state_89), classId := 3 },
                       { item := (state_90), classId := 15 }]
                     nodup := by
                       letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_7.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_7.arena.stateFintype
                       change ([(state_59), (state_60), (state_61), (state_62), (state_63), (state_64), (state_65), (state_66), (state_67), (state_68), (state_69), (state_70), (state_71), (state_72), (state_73), (state_74), (state_75), (state_76), (state_77), (state_78), (state_79), (state_80), (state_81), (state_82), (state_83), (state_84), (state_85), (state_86), (state_87), (state_88), (state_89), (state_90)] : List (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_7.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_7.arena.stateFintype
                       change ∀ x : (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM), x ∈ [(state_59), (state_60), (state_61), (state_62), (state_63), (state_64), (state_65), (state_66), (state_67), (state_68), (state_69), (state_70), (state_71), (state_72), (state_73), (state_74), (state_75), (state_76), (state_77), (state_78), (state_79), (state_80), (state_81), (state_82), (state_83), (state_84), (state_85), (state_86), (state_87), (state_88), (state_89), (state_90)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI : DecidableEq (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_7.arena.stateDecidableEq; letI : Fintype (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) := catalog_7.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

end Reg.Catalogs.SharedInformationRoot.SealedCatalog
