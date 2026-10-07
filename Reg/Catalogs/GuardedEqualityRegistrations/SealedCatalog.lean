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
import Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification
import Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

namespace Reg.Catalogs.GuardedEqualityRegistrations.SealedCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.GuardedEqualityRegistrations.SealedCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model), theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena, statementIdentity := some "sha256:ff72989c2b45d52570a4d716b0ba5064b872ce6bd51d804858fc59ab4b2c0e58", registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification },
    { statement := (_), proof := (@_root_.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer), theoremName := `D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena, statementIdentity := some "sha256:a2696beef1ce0e3cb782708559f90acd25415caf6cf673804746e92d6fbcc2a1", registrationModuleName := `Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model), theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena, statementIdentity := some "sha256:ff72989c2b45d52570a4d716b0ba5064b872ce6bd51d804858fc59ab4b2c0e58", registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification },
    { statement := (_), proof := (@_root_.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer), theoremName := `D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena, statementIdentity := some "sha256:a2696beef1ce0e3cb782708559f90acd25415caf6cf673804746e92d6fbcc2a1", registrationModuleName := `Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups }],
  baseline := #[],
  companionPrefix := some `Reg.Catalogs.GuardedEqualityRegistrations } }

noncomputable def catalog_0 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionRealization)), Statement := _, proof := (@_root_.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 6
      stateCardEq := by decide +kernel
      full := 14
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 16, uniqueEq := by decide +kernel, without := 30, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionRealization)), Statement := _, proof := (@_root_.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionRealization)), Statement := _, proof := (@_root_.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := {
        states := ([(@Fin.mk (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (nat_lit 0)
  (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
    (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
      (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
        (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
          (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (nat_lit 1)
  (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
    (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
      (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
        (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
          (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (nat_lit 2)
  (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
    (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
      (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (nat_lit 3)
  (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
    (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (nat_lit 4)
  (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (nat_lit 5)
  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))] : List (Fin (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena).toArena).stateFintype; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena).toArena).stateFintype; decide +kernel }
    }

noncomputable def facts_0 : Contract.SealFacts catalog_0 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimension_bridge.toTheoremUnit
           D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer), correct := by rfl }]
             complete := rfl }

noncomputable def view_0 : Contract.SealCatalogView := { catalog := catalog_0, facts := facts_0 }

noncomputable def catalog_1 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 3
      stateCardEq := by decide +kernel
      full := 0
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 6, uniqueEq := by decide +kernel, without := 6, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := {
        states := ([(@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 0)
  (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 1)
  (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (nat_lit 2)
  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))] : List (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena).toArena).stateFintype; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena).toArena).stateFintype; decide +kernel }
    }

noncomputable def facts_1 : Contract.SealFacts catalog_1 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirst_bridge.toTheoremUnit
           D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model), correct := by rfl }]
             complete := rfl }

noncomputable def view_1 : Contract.SealCatalogView := { catalog := catalog_1, facts := facts_1 }

noncomputable def «seal» : Contract.Seal := {
  rootId := `Reg.Catalogs.GuardedEqualityRegistrations.SealedCatalog
  catalogs := #[
    view_0,
    view_1
  ]
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.Catalogs.GuardedEqualityRegistrations.SealedCatalog
