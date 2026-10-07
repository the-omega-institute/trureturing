import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates
open RegistrationTemplates LeanInformationAudit
noncomputable def _root_.Reg.Support.MapInjectiveRegistrationTemplates.enrollment_1 : LeanInformationAudit.Contract.TemplateEnrollment.{2, max (max 0 0) 0} (@_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization) := {
  name := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization, version := 1, constructors := #[{ name := `D5.S0.History.Marker, type := (D5.S0.History.Marker) }, { name := `D5.S0.History.Opcode, type := (D5.S0.History.Opcode) }],
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  bodyFact := `Reg.Support.MapInjectiveRegistrationTemplates.enrollment_1.bodyFact,
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates, declaration := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization, part := .type, path := [], levels := [] },
    { owner := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates, declaration := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization, part := .value, path := [], levels := [] },
    { owner := `D5.S0.History.HistoryCarrier, declaration := `D5.S0.History.Marker, part := .type, path := [], levels := [] },
    { owner := `D5.S0.History.HistoryCarrier, declaration := `D5.S0.History.Opcode, part := .type, path := [], levels := [] }], facts := [] } }

end

noncomputable def Reg.Support.MapInjectiveRegistrationTemplates.enrollment_1.bodyFact : LeanInformationAudit.Contract.NodeFact :=
  compiled_exact% "{\"declaration\":[\"Reg\",\"Support\",\"MapInjectiveRegistrationTemplates\",\"enrollment_1\"],\"part\":\"type\",\"path\":[\"argument\"],\"levels\":[]}" "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"MapInjectiveRegistrationTemplates\",\"mapInjectiveRealization\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"
