import Reg.D5.S0.Certificates.SkeletonChannelRetraction
import LeanInformationAuditInterface.Contract.Catalog
import Mathlib.Tactic.FinCases

namespace LeanInformationAuditRegTests.ContractSealFixtures.Reg.Catalogs.PointwiseDisequality.SealedCatalog
open LeanInformationAudit

def catalog : Contract.RootCatalog := { data := {
  rootId := `LeanInformationAuditRegTests.ContractSealFixtures.Reg.Catalogs.PointwiseDisequality.SealedCatalog
  expected := #[
    { statement := _, proof := D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two,
      theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two,
      objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena,
      statementIdentity := some "sha256:5d44afb033ddb3092bb7a2e8025826dbb3617a6a8c332bfe7ea171362b77ead2",
      registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction },
    { statement := _, proof := D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero,
      theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero,
      objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena,
      statementIdentity := some "sha256:7af706b36940ff69c2a70352c0a715b51cd4cac8c3d1ee9c762770d82221d2b4",
      registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction }]
  source := #[
    { statement := _, proof := D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two,
      theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two,
      objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena,
      statementIdentity := some "sha256:5d44afb033ddb3092bb7a2e8025826dbb3617a6a8c332bfe7ea171362b77ead2",
      registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction },
    { statement := _, proof := D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero,
      theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero,
      objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena,
      statementIdentity := some "sha256:7af706b36940ff69c2a70352c0a715b51cd4cac8c3d1ee9c762770d82221d2b4",
      registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction }]
  baseline := #[]
  companionPrefix := some `Reg.Catalogs.PointwiseDisequalityRegistrations } }

noncomputable def sealEntry : Contract.Seal.{0,0} := {
  rootId := `LeanInformationAuditRegTests.ContractSealFixtures.Reg.Catalogs.PointwiseDisequality.SealedCatalog
  catalogs := #[
    {
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
      enumeration := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena).toArena).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena).toArena).stateDecidableEq; exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩
    }
  ]
  options := #[] }

end LeanInformationAuditRegTests.ContractSealFixtures.Reg.Catalogs.PointwiseDisequality.SealedCatalog
