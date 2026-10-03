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
import Reg.D5.S0.History.Coding.EventCodeIntertranslation
import Reg.D5.S3.QuantumContext.ProjectionValuationObstruction

namespace Reg.Catalogs.MapInjectiveRegistrations.SealedCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.MapInjectiveRegistrations.SealedCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective), theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena, statementIdentity := some "sha256:a8a72984ee6e03fd422c616af7b7d089aa74da390c05f7710cbbbda1537b4e48", registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation },
    { statement := (_), proof := (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective), theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena, statementIdentity := some "sha256:f6c867468f7db617eb31f910b6c94236158ff940a852c72020b35a0b813d1521", registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation },
    { statement := (_), proof := (@_root_.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective), theoremName := `D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena, statementIdentity := some "sha256:f03e68530cb8bea7d2c635a151ac9a19cafa007d9c4b3c8919636eac11b477f8", registrationModuleName := `Reg.D5.S3.QuantumContext.ProjectionValuationObstruction }],
  source := #[{ statement := (_), proof := (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective), theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena, statementIdentity := some "sha256:a8a72984ee6e03fd422c616af7b7d089aa74da390c05f7710cbbbda1537b4e48", registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation },
    { statement := (_), proof := (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective), theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena, statementIdentity := some "sha256:f6c867468f7db617eb31f910b6c94236158ff940a852c72020b35a0b813d1521", registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation },
    { statement := (_), proof := (@_root_.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective), theoremName := `D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena, statementIdentity := some "sha256:f03e68530cb8bea7d2c635a151ac9a19cafa007d9c4b3c8919636eac11b477f8", registrationModuleName := `Reg.D5.S3.QuantumContext.ProjectionValuationObstruction }],
  baseline := #[],
  companionPrefix := some `Reg.Catalogs.MapInjectiveRegistrations } }

def «seal» : Contract.Seal := { rootId := `Reg.Catalogs.MapInjectiveRegistrations.SealedCatalog, options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxRecDepth, value := .nat 100000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.Catalogs.MapInjectiveRegistrations.SealedCatalog
