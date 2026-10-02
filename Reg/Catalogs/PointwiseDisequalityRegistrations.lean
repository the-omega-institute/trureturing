import Reg.D5.S0.Certificates.SkeletonChannelRetraction
import LeanInformationAuditInterface.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.RegistrationWitnesses

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.Catalogs.PointwiseDisequalityRegistrations
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena, theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two,
      statementIdentity := "sha256:5d44afb033ddb3092bb7a2e8025826dbb3617a6a8c332bfe7ea171362b77ead2",
      registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena, theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero,
      statementIdentity := "sha256:7af706b36940ff69c2a70352c0a715b51cd4cac8c3d1ee9c762770d82221d2b4",
      registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena, theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two,
      statementIdentity := "sha256:5d44afb033ddb3092bb7a2e8025826dbb3617a6a8c332bfe7ea171362b77ead2",
      registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena, theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero,
      statementIdentity := "sha256:7af706b36940ff69c2a70352c0a715b51cd4cac8c3d1ee9c762770d82221d2b4",
      registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction }]
  companionPrefix := some `Reg.Catalogs.PointwiseDisequalityRegistrations }

#seal_information_theory


section
open LeanInformationAudit
end
