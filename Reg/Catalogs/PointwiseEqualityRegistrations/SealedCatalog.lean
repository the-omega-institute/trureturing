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

noncomputable def «seal» : Contract.Seal := {
  rootId := `Reg.Catalogs.PointwiseEqualityRegistrations.SealedCatalog
  catalogs := #[
    {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterRealization)), Statement := _, proof := (@_root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      rows := Fin.cases ({ conclusion := .zero (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel) (by exact of_not_not ((not_congr ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterRealization)), Statement := _, proof := (@_root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction) }]).lowersEscape_iff_not_mem_semanticClosureWithout 0 (by decide +kernel))).mp (((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterRealization)), Statement := _, proof := (@_root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction) }]).trivialInCatalog_iff_not_lowersEscape 0 (by decide +kernel)).mp (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel)))) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .redundant (by exact ⟨0, by decide +kernel⟩)
      enumeration := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena).toArena).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena).toArena).stateDecidableEq; exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩
    },
    {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionRealization)), Statement := _, proof := (@_root_.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      rows := Fin.cases ({ conclusion := .positive (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionRealization)), Statement := _, proof := (@_root_.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionRealization)), Statement := _, proof := (@_root_.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena).toArena).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena).toArena).stateDecidableEq; exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩
    }
  ]
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.Catalogs.PointwiseEqualityRegistrations.SealedCatalog
