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

def «seal» : Contract.Seal := { rootId := `Reg.Catalogs.PointwiseDisequalityRegistrations.SealedCatalog, options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.Catalogs.PointwiseDisequalityRegistrations.SealedCatalog
