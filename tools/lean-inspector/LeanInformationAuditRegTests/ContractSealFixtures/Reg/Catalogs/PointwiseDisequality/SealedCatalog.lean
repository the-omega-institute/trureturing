import Reg.D5.S0.Certificates.SkeletonChannelRetraction
import LeanInformationAuditInterface.Contract.Catalog

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

def sealEntry : Contract.Seal := {
  rootId := `LeanInformationAuditRegTests.ContractSealFixtures.Reg.Catalogs.PointwiseDisequality.SealedCatalog
  options := #[] }

end LeanInformationAuditRegTests.ContractSealFixtures.Reg.Catalogs.PointwiseDisequality.SealedCatalog
