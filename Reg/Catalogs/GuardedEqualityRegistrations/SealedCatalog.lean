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

noncomputable def «seal» : Contract.Seal := {
  rootId := `Reg.Catalogs.GuardedEqualityRegistrations.SealedCatalog
  catalogs := #[
    {
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
      enumeration := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena).toArena).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena).toArena).stateDecidableEq; exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩
    },
    {
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
      enumeration := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena).toArena).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena).toArena).stateDecidableEq; exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩
    }
  ]
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.Catalogs.GuardedEqualityRegistrations.SealedCatalog
