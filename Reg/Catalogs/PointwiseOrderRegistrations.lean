import Reg.D5.S1.Words.Powers.GoldenDesubstitution
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
  rootId := `Reg.Catalogs.PointwiseOrderRegistrations
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, theoremName := `D5.S1.Words.Powers.substLength_pos,
      statementIdentity := "sha256:c7c23089a7484f261005f23167c5b1588d1b6c64d15914dbdc36e4fe672715db",
      registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, theoremName := `D5.S1.Words.Powers.substLength_le_two,
      statementIdentity := "sha256:17684442190c21bc68cd745b6c7fb89435f2c2c21f60801dbbb02dbc9e3b6eec",
      registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, theoremName := `D5.S1.Words.Powers.substLength_pos,
      statementIdentity := "sha256:c7c23089a7484f261005f23167c5b1588d1b6c64d15914dbdc36e4fe672715db",
      registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, theoremName := `D5.S1.Words.Powers.substLength_le_two,
      statementIdentity := "sha256:17684442190c21bc68cd745b6c7fb89435f2c2c21f60801dbbb02dbc9e3b6eec",
      registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution }]
  companionPrefix := some `Reg.Catalogs.PointwiseOrderRegistrations }

#seal_information_theory


section
open LeanInformationAudit
end
