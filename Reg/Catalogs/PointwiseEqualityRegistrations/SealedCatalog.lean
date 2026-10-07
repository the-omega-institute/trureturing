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
import Reg.D5.S0.Tower.DBonacci.Substitution
import Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates

namespace Reg.Catalogs.PointwiseEqualityRegistrations.SealedCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.PointwiseEqualityRegistrations.SealedCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible), theoremName := `D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena, statementIdentity := some "sha256:b30ce4d291640ad8d50484250e17905625944a4356233ef3b10bb285576eb0e0", registrationModuleName := `Reg.D5.S0.Tower.DBonacci.Substitution },
    { statement := (_), proof := (@_root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction), theoremName := `D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena, statementIdentity := some "sha256:3cedb82534e585ab1c5cb122ef9b78447ce5288c441f3c5cde230fe1ea477fcc", registrationModuleName := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates }],
  source := #[{ statement := (_), proof := (@_root_.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible), theoremName := `D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena, statementIdentity := some "sha256:b30ce4d291640ad8d50484250e17905625944a4356233ef3b10bb285576eb0e0", registrationModuleName := `Reg.D5.S0.Tower.DBonacci.Substitution },
    { statement := (_), proof := (@_root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction), theoremName := `D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena, statementIdentity := some "sha256:3cedb82534e585ab1c5cb122ef9b78447ce5288c441f3c5cde230fe1ea477fcc", registrationModuleName := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates }],
  baseline := #[],
  companionPrefix := some `Reg.Catalogs.PointwiseEqualityRegistrations } }

noncomputable def catalog_0 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterRealization)), Statement := _, proof := (@_root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 3
      stateCardEq := by decide +kernel
      full := 6
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 0, uniqueEq := by decide +kernel, without := 6, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .zero rfl (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel) (by exact of_not_not ((not_congr ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterRealization)), Statement := _, proof := (@_root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction) }]).lowersEscape_iff_not_mem_semanticClosureWithout 0 (by decide +kernel))).mp (((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterRealization)), Statement := _, proof := (@_root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction) }]).trivialInCatalog_iff_not_lowersEscape 0 (by decide +kernel)).mp (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel)))) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .redundant (by exact ⟨0, by decide +kernel⟩)
      enumeration := {
        states := ([(@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 0)
  (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 1)
  (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 2)
  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))] : List (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena).toArena).stateFintype; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena).toArena).stateFintype; decide +kernel }
    }

noncomputable def facts_0 : Contract.SealFacts catalog_0 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenter_bridge.toTheoremUnit
           D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 0
        uniqueEq := ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq).trans (by rfl)
        without := 6
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
                 D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena.State
                 (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
                   (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                   (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                   (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                 D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena.State
                 (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
                   (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                   (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                   (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
               Bool.true), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          Bool.false), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          Bool.false)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          Bool.false)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  decide +kernel }
      partition := { rows := [{ item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 0)
               (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                 (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                   (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), classId := 0 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 1)
               (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))), classId := 0 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 2)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))), classId := 0 }]
                     nodup := by
                       letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype
                       change ([(@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 0)
               (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                 (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                   (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 1)
               (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 2)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))] : List (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))).Nodup
                       decide +kernel
                     complete := by
                       letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype
                       change ∀ x : (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))), x ∈ [(@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 0)
               (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                 (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                   (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 1)
               (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 2)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))]
                       decide +kernel
                     classes := by letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

noncomputable def view_0 : Contract.SealCatalogView := { catalog := catalog_0, facts := facts_0 }

noncomputable def catalog_1 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionRealization)), Statement := _, proof := (@_root_.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 3
      stateCardEq := by decide +kernel
      full := 0
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 6, uniqueEq := by decide +kernel, without := 6, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionRealization)), Statement := _, proof := (@_root_.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionRealization)), Statement := _, proof := (@_root_.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := {
        states := ([(@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 0)
  (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 1)
  (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 2)
  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))] : List (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena).toArena).stateFintype; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena).toArena).stateFintype; decide +kernel }
    }

noncomputable def facts_1 : Contract.SealFacts catalog_1 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitution_bridge.toTheoremUnit
           D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 6
        uniqueEq := ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).uniqueEq).trans (by rfl)
        without := 6
        withoutEq := ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0]) bucket)
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
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
                 D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena.State
                 (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
                   (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                   (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                   (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                 D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena.State
                 (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
                   (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                   (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                   (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
               Bool.true), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          Bool.false), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          Bool.false)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexFintype)
                  decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          Bool.false)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexFintype)
                  decide +kernel }
      partition := { rows := [{ item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 0)
               (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                 (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                   (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), classId := 0 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 1)
               (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))), classId := 1 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 2)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))), classId := 2 }]
                     nodup := by
                       letI := catalog_1.arena.stateDecidableEq; letI := catalog_1.arena.stateFintype
                       change ([(@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 0)
               (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                 (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                   (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 1)
               (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 2)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))] : List (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))).Nodup
                       decide +kernel
                     complete := by
                       letI := catalog_1.arena.stateDecidableEq; letI := catalog_1.arena.stateFintype
                       change ∀ x : (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))), x ∈ [(@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 0)
               (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                 (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                   (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 1)
               (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 2)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))]
                       decide +kernel
                     classes := by letI := catalog_1.arena.stateDecidableEq; letI := catalog_1.arena.stateFintype; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

noncomputable def view_1 : Contract.SealCatalogView := { catalog := catalog_1, facts := facts_1 }

noncomputable def «seal» : Contract.Seal := {
  rootId := `Reg.Catalogs.PointwiseEqualityRegistrations.SealedCatalog
  catalogs := #[
    view_0,
    view_1
  ]
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.Catalogs.PointwiseEqualityRegistrations.SealedCatalog
