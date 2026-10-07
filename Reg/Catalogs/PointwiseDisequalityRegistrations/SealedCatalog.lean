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
import Reg.D5.S0.Certificates.SkeletonChannelRetraction

namespace Reg.Catalogs.PointwiseDisequalityRegistrations.SealedCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.PointwiseDisequalityRegistrations.SealedCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two), theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena, statementIdentity := some "sha256:5d44afb033ddb3092bb7a2e8025826dbb3617a6a8c332bfe7ea171362b77ead2", registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction },
    { statement := (_), proof := (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero), theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena, statementIdentity := some "sha256:7af706b36940ff69c2a70352c0a715b51cd4cac8c3d1ee9c762770d82221d2b4", registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction }],
  source := #[{ statement := (_), proof := (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two), theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena, statementIdentity := some "sha256:5d44afb033ddb3092bb7a2e8025826dbb3617a6a8c332bfe7ea171362b77ead2", registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction },
    { statement := (_), proof := (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero), theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena, statementIdentity := some "sha256:7af706b36940ff69c2a70352c0a715b51cd4cac8c3d1ee9c762770d82221d2b4", registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction }],
  baseline := #[],
  companionPrefix := some `Reg.Catalogs.PointwiseDisequalityRegistrations } }

noncomputable def catalog_0 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena).toArena
      size := 2
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.recurrentRealization)), Statement := _, proof := (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.transientRealization)), Statement := _, proof := (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 4
      stateCardEq := by decide +kernel
      full := 0
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 2, uniqueEq := by decide +kernel, without := 2, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.recurrentRealization)), Statement := _, proof := (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.transientRealization)), Statement := _, proof := (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (Fin.cases ({ unique := 2, uniqueEq := by decide +kernel, without := 2, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.recurrentRealization)), Statement := _, proof := (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.transientRealization)), Statement := _, proof := (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero) }]).lowersEscape_iff_uniqueCaptureCount_pos 1 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i))
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.recurrentRealization)), Statement := _, proof := (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.transientRealization)), Statement := _, proof := (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.recurrentRealization)), Statement := _, proof := (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.transientRealization)), Statement := _, proof := (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero) }]).lowersEscape_iff_uniqueCaptureCount_pos 1 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := {
        states := ([(@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 0)
  (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 1)
  (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 2)
  (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 3)
  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))] : List (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena).toArena).stateFintype; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena).toArena).stateFintype; decide +kernel }
    }

noncomputable def facts_0 : Contract.SealFacts catalog_0 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.recurrent_bridge.toTheoremUnit
           D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two), correct := by rfl }, { position := 1, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.transient_bridge.toTheoremUnit
                                 D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 2
        uniqueEq := ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq).trans (by rfl)
        without := 2
        withoutEq := ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_0.nondegenerate).mpr
          rw [(catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq]
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
                 D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
                 (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
                   (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                   (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                   (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                 D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
                 (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
                   (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                   (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                   (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
               Bool.true), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          Bool.false), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          Bool.false)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          Bool.false)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  decide +kernel }
      partition := { rows := [{ item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 0)
               (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                 (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                   (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                     (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))), classId := 0 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 1)
               (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                 (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                   (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))), classId := 1 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 2)
               (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))), classId := 0 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 3)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))), classId := 2 }]
                     nodup := by
                       letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype
                       change ([(@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 0)
               (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                 (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                   (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                     (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 1)
               (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                 (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                   (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 2)
               (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 3)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))] : List (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))).Nodup
                       decide +kernel
                     complete := by
                       letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype
                       change ∀ x : (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))), x ∈ [(@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 0)
               (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                 (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                   (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                     (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 1)
               (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                 (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                   (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 2)
               (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 3)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))]
                       decide +kernel
                     classes := by letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype; decide +kernel }
      stateOrder := by rfl },
    {
      position := 1
      within := by decide +kernel
      row := {
        unique := 2
        uniqueEq := ((catalog_0.rows (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq).trans (by rfl)
        without := 2
        withoutEq := ((catalog_0.rows (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_0.rows (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_0.rows (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]) bucket)
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
                 D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
                 (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
                   (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                   (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                   (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                 D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
                 (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
                   (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                   (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                   (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
               Bool.true), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          Bool.false), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          Bool.false)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          Bool.false)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨1, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  decide +kernel }
      partition := { rows := [{ item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 0)
               (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                 (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                   (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                     (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))), classId := 0 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 1)
               (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                 (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                   (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))), classId := 0 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 2)
               (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))), classId := 1 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 3)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))), classId := 2 }]
                     nodup := by
                       letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype
                       change ([(@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 0)
               (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                 (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                   (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                     (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 1)
               (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                 (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                   (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 2)
               (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 3)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))] : List (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))).Nodup
                       decide +kernel
                     complete := by
                       letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype
                       change ∀ x : (Fin (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))), x ∈ [(@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 0)
               (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                 (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                   (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                     (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 1)
               (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                 (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                   (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 2)
               (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 3)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))]
                       decide +kernel
                     classes := by letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

noncomputable def view_0 : Contract.SealCatalogView := { catalog := catalog_0, facts := facts_0 }

noncomputable def «seal» : Contract.Seal := {
  rootId := `Reg.Catalogs.PointwiseDisequalityRegistrations.SealedCatalog
  catalogs := #[
    view_0
  ]
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.Catalogs.PointwiseDisequalityRegistrations.SealedCatalog
