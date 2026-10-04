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
import Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape
import Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability

namespace Reg.Catalogs.ExistentialWitnessRegistrations.SealedCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.ExistentialWitnessRegistrations.SealedCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint), theoremName := `D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena, statementIdentity := some "sha256:6229f4053788af2b620d04f5df8b8ead8963f1ffb30952697ec73dca847c6886", registrationModuleName := `Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts), theoremName := `D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena, statementIdentity := some "sha256:9fe223b46afd61e89e3883878aabd3f4184a39542015b7c4e40ec8c599a7c46c", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability }],
  source := #[{ statement := (_), proof := (@_root_.D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint), theoremName := `D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena, statementIdentity := some "sha256:6229f4053788af2b620d04f5df8b8ead8963f1ffb30952697ec73dca847c6886", registrationModuleName := `Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts), theoremName := `D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena, statementIdentity := some "sha256:9fe223b46afd61e89e3883878aabd3f4184a39542015b7c4e40ec8c599a7c46c", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability }],
  baseline := #[],
  companionPrefix := some `Reg.Catalogs.ExistentialWitnessRegistrations } }

def «seal» : Contract.Seal := { rootId := `Reg.Catalogs.ExistentialWitnessRegistrations.SealedCatalog, options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxRecDepth, value := .nat 100000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.Catalogs.ExistentialWitnessRegistrations.SealedCatalog
