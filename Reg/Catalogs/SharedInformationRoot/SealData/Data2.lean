import Mathlib.Data.Fin.VecNotation
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.CIRPT.PrimitiveKernel
import D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
import D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
import Reg.Catalogs.InformationRoot.SealedCatalog
import Reg.Support.LegacyCausalCoordinates
import Reg.Support.LegacyCausalFinite
import Reg.Support.LegacyCausalSlots
import Reg.Support.LegacyContextReplacement
import Reg.Support.LegacyGluing

set_option backward.isDefEq.respectTransparency.types false

namespace Reg.Catalogs.SharedInformationRoot.SealedCatalog
open LeanInformationAudit

noncomputable def catalog_2 : Contract.SealCatalog := {
      arenaName := `Reg.Support.LegacyCausalCoordinates.icObjectArena
      catalogId := `Reg.Support.LegacyCausalCoordinates.icObjectArena
      arena := (_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena)
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.localActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[1]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[1]'(by decide))).catalog.bundleNonempty
      stateCard := 16
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[1]'(by decide))).catalog.stateCardEq
      full := 0
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[1]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[1]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[1]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
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

noncomputable def facts_2 : Contract.SealFacts catalog_2 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyCausalFinite.local_bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 240
        uniqueEq := ((catalog_2.rows (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).uniqueEq).trans (by rfl)
        without := 240
        withoutEq := ((catalog_2.rows (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_2.rows (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_2.rows (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0]) bucket)
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.Index); exact (catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.Index); exact (catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.indexFintype)
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.Index); exact (catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.Index); exact (catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.indexFintype)
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
                       letI := catalog_2.arena.stateDecidableEq; letI := catalog_2.arena.stateFintype
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
                       letI := catalog_2.arena.stateDecidableEq; letI := catalog_2.arena.stateFintype
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
                     classes := by letI := catalog_2.arena.stateDecidableEq; letI := catalog_2.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

noncomputable def catalog_3 : Contract.SealCatalog := {
      arenaName := `Reg.Support.LegacyContextReplacement.objectArena
      catalogId := `Reg.Support.LegacyContextReplacement.objectArena
      arena := (_root_.Reg.Support.LegacyContextReplacement.objectArena)
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyContextReplacement.objectArena)).stateDecidableEq (Reg.Support.LegacyContextReplacement.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[2]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[2]'(by decide))).catalog.bundleNonempty
      stateCard := 8
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[2]'(by decide))).catalog.stateCardEq
      full := 0
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[2]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[2]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[2]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := {
        states := ([(@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false))] : List (Prod Bool (Prod Bool Bool)))
        nodup := by letI := ((_root_.Reg.Support.LegacyContextReplacement.objectArena)).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyContextReplacement.objectArena)).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.Reg.Support.LegacyContextReplacement.objectArena)).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyContextReplacement.objectArena)).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_3 : Contract.SealFacts catalog_3 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyContextReplacement.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 56
        uniqueEq := ((catalog_3.rows (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).uniqueEq).trans (by rfl)
        without := 56
        withoutEq := ((catalog_3.rows (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_3.rows (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_3.rows (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_3.nondegenerate).mpr
          rw [(catalog_3.rows (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).uniqueEq]
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_3.units (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).primitives.Index); exact (catalog_3.units (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_3.units (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).primitives.Index); exact (catalog_3.units (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).primitives.indexFintype)
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
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_3.units (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).primitives.Index); exact (catalog_3.units (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_3.units (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).primitives.Index); exact (catalog_3.units (⟨0, by decide +kernel⟩ : Fin catalog_3.size)).primitives.indexFintype)
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
      arenaName := `Reg.Support.LegacyGluing.arena
      catalogId := `Reg.Support.LegacyGluing.arena
      arena := (_root_.Reg.Support.LegacyGluing.arena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyGluing.arena).toArena).stateDecidableEq (Reg.Support.LegacyGluing.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[3]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[3]'(by decide))).catalog.bundleNonempty
      stateCard := 8
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[3]'(by decide))).catalog.stateCardEq
      full := 8
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[3]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[3]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[3]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := {
        states := ([(@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)), (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false))] : List (Prod Bool (Prod Bool Bool)))
        nodup := by letI := ((_root_.Reg.Support.LegacyGluing.arena).toArena).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyGluing.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.Reg.Support.LegacyGluing.arena).toArena).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyGluing.arena).toArena).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

end Reg.Catalogs.SharedInformationRoot.SealedCatalog
