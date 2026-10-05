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
import Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain
import Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling

namespace Reg.Catalogs.IffRegistrations.SealedCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.IffRegistrations.SealedCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled), theoremName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, statementIdentity := some "sha256:48183359aa256091e3dfc2a80a5352b99a62f3ff03446236a0e6d9bd82fa988e", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling },
    { statement := (_), proof := (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff), theoremName := `D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena, statementIdentity := some "sha256:76175c4656a4be731bad802d770e51ed7e427531bf5c0a2577c86dd338299e1f", registrationModuleName := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled), theoremName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, statementIdentity := some "sha256:48183359aa256091e3dfc2a80a5352b99a62f3ff03446236a0e6d9bd82fa988e", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling },
    { statement := (_), proof := (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff), theoremName := `D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena, statementIdentity := some "sha256:76175c4656a4be731bad802d770e51ed7e427531bf5c0a2577c86dd338299e1f", registrationModuleName := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain }],
  baseline := #[],
  companionPrefix := some `Reg.Catalogs.IffRegistrations } }

noncomputable def «seal» : Contract.Seal := {
  rootId := `Reg.Catalogs.IffRegistrations.SealedCatalog
  catalogs := #[
    {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualRealization)), Statement := _, proof := (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 4
      stateCardEq := by decide +kernel
      full := 4
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 8, uniqueEq := by decide +kernel, without := 12, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualRealization)), Statement := _, proof := (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualRealization)), Statement := _, proof := (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena).toArena).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena).toArena).stateDecidableEq; exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩
    },
    {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 5
      stateCardEq := by decide +kernel
      full := 12
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 8, uniqueEq := by decide +kernel, without := 20, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena).toArena).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena).toArena).stateDecidableEq; exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩
    }
  ]
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.Catalogs.IffRegistrations.SealedCatalog
