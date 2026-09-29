import Reg.D5.S0.History.Coding.EventCodeIntertranslation
import Reg.D5.S3.QuantumContext.ProjectionValuationObstruction
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
  rootId := `Reg.Catalogs.MapInjectiveRegistrations
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena, theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective,
      statementIdentity := "sha256:a8a72984ee6e03fd422c616af7b7d089aa74da390c05f7710cbbbda1537b4e48",
      registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena, theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective,
      statementIdentity := "sha256:f6c867468f7db617eb31f910b6c94236158ff940a852c72020b35a0b813d1521",
      registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena, theoremName := `D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective,
      statementIdentity := "sha256:f03e68530cb8bea7d2c635a151ac9a19cafa007d9c4b3c8919636eac11b477f8",
      registrationModuleName := `Reg.D5.S3.QuantumContext.ProjectionValuationObstruction }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena, theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective,
      statementIdentity := "sha256:a8a72984ee6e03fd422c616af7b7d089aa74da390c05f7710cbbbda1537b4e48",
      registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena, theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective,
      statementIdentity := "sha256:f6c867468f7db617eb31f910b6c94236158ff940a852c72020b35a0b813d1521",
      registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena, theoremName := `D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective,
      statementIdentity := "sha256:f03e68530cb8bea7d2c635a151ac9a19cafa007d9c4b3c8919636eac11b477f8",
      registrationModuleName := `Reg.D5.S3.QuantumContext.ProjectionValuationObstruction }]
  companionPrefix := some `Reg.Catalogs.MapInjectiveRegistrations }

set_option maxRecDepth 100000 in
#seal_information_theory


section
open LeanInformationAudit
end
