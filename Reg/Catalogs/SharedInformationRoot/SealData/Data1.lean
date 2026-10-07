import Mathlib.Data.Fin.VecNotation
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.Aggregation.AgendaPower
import D5.S3.ConceptDynamics.CIRPT.PrimitiveKernel
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
import D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
import Reg.Catalogs.InformationRoot.SealedCatalog
import Reg.Catalogs.SharedInformationRoot.SealData.Data0
import Reg.Catalogs.SharedInformationRoot.SealData.States0
import Reg.Support.LegacyAgenda
import Reg.Support.LegacyCausalCoordinates
import Reg.Support.LegacyCausalFinite
import Reg.Support.LegacyCausalSlots
import Reg.Support.LegacyFiniteTransport

set_option backward.isDefEq.respectTransparency.types false

namespace Reg.Catalogs.SharedInformationRoot.SealedCatalog
open LeanInformationAudit

noncomputable def facts_0_row_1 : Contract.SealFactRow catalog_0 :=
  {
      position := 1
      within := by decide +kernel
      row := {
        unique := 968
        uniqueEq := ((catalog_0.rows (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq).trans (by rfl)
        without := 992
        withoutEq := ((catalog_0.rows (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 968, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_0.rows (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_0.rows (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 968, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_0.nondegenerate).mpr
          rw [(catalog_0.rows (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq]
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
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
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
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
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
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 2)
            (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 3)
            (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 4)
            (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 5)
            (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 6)
            (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 7)
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
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
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 1)
            (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 2)
            (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 3)
            (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 4)
            (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 5)
            (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 6)
            (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 7)
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b)))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
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
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 1)
            (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 2)
            (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 3)
            (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 4)
            (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 5)
            (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 6)
            (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 7)
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)))), classId := 0 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)))), classId := 0 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)))), classId := 0 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)))), classId := 0 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)))), classId := 0 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)))), classId := 0 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)))), classId := 0 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)))), classId := 0 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)))), classId := 0 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)))), classId := 0 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)))), classId := 0 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)))), classId := 0 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)))), classId := 0 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)))), classId := 0 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)))), classId := 0 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)))), classId := 0 },
                       { item := (state_0), classId := 1 },
                       { item := (state_1), classId := 2 },
                       { item := (state_2), classId := 1 },
                       { item := (state_3), classId := 2 },
                       { item := (state_4), classId := 3 },
                       { item := (state_5), classId := 4 },
                       { item := (state_6), classId := 5 },
                       { item := (state_7), classId := 6 },
                       { item := (state_8), classId := 7 },
                       { item := (state_9), classId := 8 },
                       { item := (state_10), classId := 9 },
                       { item := (state_11), classId := 10 },
                       { item := (state_12), classId := 11 },
                       { item := (state_13), classId := 11 },
                       { item := (state_14), classId := 12 },
                       { item := (state_15), classId := 12 },
                       { item := (state_16), classId := 1 },
                       { item := (state_17), classId := 13 },
                       { item := (state_18), classId := 14 },
                       { item := (state_19), classId := 11 },
                       { item := (state_20), classId := 15 },
                       { item := (state_21), classId := 16 },
                       { item := (state_22), classId := 17 },
                       { item := (state_23), classId := 18 },
                       { item := (state_24), classId := 19 },
                       { item := (state_25), classId := 20 },
                       { item := (state_26), classId := 21 },
                       { item := (state_27), classId := 22 },
                       { item := (state_28), classId := 2 },
                       { item := (state_29), classId := 23 },
                       { item := (state_30), classId := 24 },
                       { item := (state_31), classId := 12 }]
                     nodup := by
                       letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype
                       change ([(@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)))), (state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15), (state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (state_26), (state_27), (state_28), (state_29), (state_30), (state_31)] : List (Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype
                       change ∀ x : (Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData), x ∈ [(@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)))), (state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15), (state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (state_26), (state_27), (state_28), (state_29), (state_30), (state_31)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }

noncomputable def facts_0 : Contract.SealFacts catalog_0 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyCausalFinite.ic_bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual), correct := by rfl }, { position := 1, within := by decide +kernel, item := (Reg.Support.LegacyCausalFinite.oi_bridge.toTheoremUnit
                                        D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention), correct := by rfl }]
             complete := rfl }
  rows := [
    facts_0_row_0,
    facts_0_row_1
  ]
  complete := rfl

noncomputable def catalog_1 : Contract.SealCatalog := {
      arenaName := `Reg.Support.LegacyAgenda.arena
      catalogId := `Reg.Support.LegacyAgenda.arena
      arena := (_root_.Reg.Support.LegacyAgenda.arena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateDecidableEq (Reg.Support.LegacyAgenda.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[0]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[0]'(by decide))).catalog.bundleNonempty
      stateCard := 27
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[0]'(by decide))).catalog.stateCardEq
      full := 132
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[0]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[0]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[0]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := {
        states := ([(state_32), (state_33), (state_34), (state_35), (state_36), (state_37), (state_38), (state_39), (state_40), (state_41), (state_42), (state_43), (state_44), (state_45), (state_46), (state_47), (state_48), (state_49), (state_50), (state_51), (state_52), (state_53), (state_54), (state_55), (state_56), (state_57), (state_58)] : List (Prod Reg.Support.LegacyFiniteTransport.Three
  (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three)))
        nodup := by letI := ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_1 : Contract.SealFacts catalog_1 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyAgenda.bridge.toTheoremUnit D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 570
        uniqueEq := ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).uniqueEq).trans (by rfl)
        without := 702
        withoutEq := ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 84, 0, 0, 0, 0, 0, 318, 0, 168, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).roleBins = ![0, 84, 0, 0, 0, 0, 0, 318, 0, 168, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_1.nondegenerate).mpr
          rw [(catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).uniqueEq]
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexFintype)
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (state_32), classId := 0 },
                       { item := (state_33), classId := 0 },
                       { item := (state_34), classId := 1 },
                       { item := (state_35), classId := 0 },
                       { item := (state_36), classId := 0 },
                       { item := (state_37), classId := 0 },
                       { item := (state_38), classId := 1 },
                       { item := (state_39), classId := 0 },
                       { item := (state_40), classId := 0 },
                       { item := (state_41), classId := 2 },
                       { item := (state_42), classId := 2 },
                       { item := (state_43), classId := 3 },
                       { item := (state_44), classId := 2 },
                       { item := (state_45), classId := 2 },
                       { item := (state_46), classId := 2 },
                       { item := (state_47), classId := 3 },
                       { item := (state_48), classId := 2 },
                       { item := (state_49), classId := 2 },
                       { item := (state_50), classId := 4 },
                       { item := (state_51), classId := 4 },
                       { item := (state_52), classId := 5 },
                       { item := (state_53), classId := 4 },
                       { item := (state_54), classId := 4 },
                       { item := (state_55), classId := 4 },
                       { item := (state_56), classId := 5 },
                       { item := (state_57), classId := 4 },
                       { item := (state_58), classId := 4 }]
                     nodup := by
                       letI := catalog_1.arena.stateDecidableEq; letI := catalog_1.arena.stateFintype
                       change ([(state_32), (state_33), (state_34), (state_35), (state_36), (state_37), (state_38), (state_39), (state_40), (state_41), (state_42), (state_43), (state_44), (state_45), (state_46), (state_47), (state_48), (state_49), (state_50), (state_51), (state_52), (state_53), (state_54), (state_55), (state_56), (state_57), (state_58)] : List (Prod Reg.Support.LegacyFiniteTransport.Three
               (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three))).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_1.arena.stateDecidableEq; letI := catalog_1.arena.stateFintype
                       change ∀ x : (Prod Reg.Support.LegacyFiniteTransport.Three
               (Prod Reg.Support.LegacyFiniteTransport.Three Reg.Support.LegacyFiniteTransport.Three)), x ∈ [(state_32), (state_33), (state_34), (state_35), (state_36), (state_37), (state_38), (state_39), (state_40), (state_41), (state_42), (state_43), (state_44), (state_45), (state_46), (state_47), (state_48), (state_49), (state_50), (state_51), (state_52), (state_53), (state_54), (state_55), (state_56), (state_57), (state_58)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_1.arena.stateDecidableEq; letI := catalog_1.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

end Reg.Catalogs.SharedInformationRoot.SealedCatalog
