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
import Reg.D5.S1.Words.Powers.GoldenDesubstitution

namespace Reg.Catalogs.PointwiseOrderRegistrations.SealedCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.PointwiseOrderRegistrations.SealedCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Powers.substLength_pos), theoremName := `D5.S1.Words.Powers.substLength_pos, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, statementIdentity := some "sha256:c7c23089a7484f261005f23167c5b1588d1b6c64d15914dbdc36e4fe672715db", registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution },
    { statement := (_), proof := (@_root_.D5.S1.Words.Powers.substLength_le_two), theoremName := `D5.S1.Words.Powers.substLength_le_two, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, statementIdentity := some "sha256:17684442190c21bc68cd745b6c7fb89435f2c2c21f60801dbbb02dbc9e3b6eec", registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution }],
  source := #[{ statement := (_), proof := (@_root_.D5.S1.Words.Powers.substLength_pos), theoremName := `D5.S1.Words.Powers.substLength_pos, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, statementIdentity := some "sha256:c7c23089a7484f261005f23167c5b1588d1b6c64d15914dbdc36e4fe672715db", registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution },
    { statement := (_), proof := (@_root_.D5.S1.Words.Powers.substLength_le_two), theoremName := `D5.S1.Words.Powers.substLength_le_two, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, statementIdentity := some "sha256:17684442190c21bc68cd745b6c7fb89435f2c2c21f60801dbbb02dbc9e3b6eec", registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution }],
  baseline := #[],
  companionPrefix := some `Reg.Catalogs.PointwiseOrderRegistrations } }

noncomputable def catalog_0 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena
      catalogId := `substitutionBounds
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena)
      size := 2
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.upperRealization)), Statement := _, proof := (@_root_.D5.S1.Words.Powers.substLength_le_two) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.positiveRealization)), Statement := _, proof := (@_root_.D5.S1.Words.Powers.substLength_pos) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 2
      stateCardEq := by decide +kernel
      full := 0
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 0, uniqueEq := by decide +kernel, without := 0, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .zero rfl (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel) (by exact of_not_not ((not_congr ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.upperRealization)), Statement := _, proof := (@_root_.D5.S1.Words.Powers.substLength_le_two) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.positiveRealization)), Statement := _, proof := (@_root_.D5.S1.Words.Powers.substLength_pos) }]).lowersEscape_iff_not_mem_semanticClosureWithout 0 (by decide +kernel))).mp (((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.upperRealization)), Statement := _, proof := (@_root_.D5.S1.Words.Powers.substLength_le_two) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.positiveRealization)), Statement := _, proof := (@_root_.D5.S1.Words.Powers.substLength_pos) }]).trivialInCatalog_iff_not_lowersEscape 0 (by decide +kernel)).mp (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel)))) }) (Fin.cases ({ unique := 0, uniqueEq := by decide +kernel, without := 0, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .zero rfl (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel) (by exact of_not_not ((not_congr ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.upperRealization)), Statement := _, proof := (@_root_.D5.S1.Words.Powers.substLength_le_two) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.positiveRealization)), Statement := _, proof := (@_root_.D5.S1.Words.Powers.substLength_pos) }]).lowersEscape_iff_not_mem_semanticClosureWithout 1 (by decide +kernel))).mp (((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.upperRealization)), Statement := _, proof := (@_root_.D5.S1.Words.Powers.substLength_le_two) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.positiveRealization)), Statement := _, proof := (@_root_.D5.S1.Words.Powers.substLength_pos) }]).trivialInCatalog_iff_not_lowersEscape 1 (by decide +kernel)).mp (by unfold _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.TrivialInCatalog; apply Finset.card_eq_zero.mp; decide +kernel)))) }) (fun i => Fin.elim0 i))
      collisions := #[⟨⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨by decide +kernel, by constructor <;> decide +kernel⟩⟩]
      conclusion := .redundant (by exact ⟨0, by decide +kernel⟩)
      enumeration := {
        states := ([(Bool.true), (Bool.false)] : List (Bool))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena)).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena)).stateFintype; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena)).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena)).stateFintype; decide +kernel }
    }

noncomputable def facts_0 : Contract.SealFacts catalog_0 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.upper_bridge.toTheoremUnit
           D5.S1.Words.Powers.substLength_le_two), correct := by rfl }, { position := 1, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.positive_bridge.toTheoremUnit
                                     D5.S1.Words.Powers.substLength_pos), correct := by rfl }]
             complete := rfl }

noncomputable def view_0 : Contract.SealCatalogView := { catalog := catalog_0, facts := facts_0 }

noncomputable def «seal» : Contract.Seal := {
  rootId := `Reg.Catalogs.PointwiseOrderRegistrations.SealedCatalog
  catalogs := #[
    view_0
  ]
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.Catalogs.PointwiseOrderRegistrations.SealedCatalog
