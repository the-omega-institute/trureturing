import Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain
import Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling
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
  rootId := `Reg.Catalogs.IffRegistrations
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, theoremName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled,
      statementIdentity := "sha256:48183359aa256091e3dfc2a80a5352b99a62f3ff03446236a0e6d9bd82fa988e",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena, theoremName := `D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff,
      statementIdentity := "sha256:76175c4656a4be731bad802d770e51ed7e427531bf5c0a2577c86dd338299e1f",
      registrationModuleName := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, theoremName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled,
      statementIdentity := "sha256:48183359aa256091e3dfc2a80a5352b99a62f3ff03446236a0e6d9bd82fa988e",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena, theoremName := `D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff,
      statementIdentity := "sha256:76175c4656a4be731bad802d770e51ed7e427531bf5c0a2577c86dd338299e1f",
      registrationModuleName := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain }]
  companionPrefix := some `Reg.Catalogs.IffRegistrations }

#seal_information_theory


section
open LeanInformationAudit
end
