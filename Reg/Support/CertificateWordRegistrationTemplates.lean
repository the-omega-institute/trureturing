import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.CertificateWordRegistrationTemplates

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.CertificateWordRegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscape
open LeanInformationAudit
noncomputable def _root_.Reg.Support.CertificateWordRegistrationTemplates.enrollment_1 : LeanInformationAudit.Contract.TemplateEnrollment.{2, 0} (@_root_.D5.S3.ConceptDynamics.InformationEscape.CertificateWordRegistrationTemplates.certificateWordRealization) := {
  name := `D5.S3.ConceptDynamics.InformationEscape.CertificateWordRegistrationTemplates.certificateWordRealization, version := 1, constructors := #[],
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  bodyFact := `Reg.Support.CertificateWordRegistrationTemplates.enrollment_1.bodyFact,
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.InformationEscape.CertificateWordRegistrationTemplates, declaration := `D5.S3.ConceptDynamics.InformationEscape.CertificateWordRegistrationTemplates.certificateWordRealization, part := .type, path := [], levels := [] },
    { owner := `D5.S3.ConceptDynamics.InformationEscape.CertificateWordRegistrationTemplates, declaration := `D5.S3.ConceptDynamics.InformationEscape.CertificateWordRegistrationTemplates.certificateWordRealization, part := .value, path := [], levels := [] }], facts := [] } }

end

noncomputable def Reg.Support.CertificateWordRegistrationTemplates.enrollment_1.bodyFact : LeanInformationAudit.Contract.NodeFact :=
  compiled_exact% "{\"declaration\":[\"Reg\",\"Support\",\"CertificateWordRegistrationTemplates\",\"enrollment_1\"],\"part\":\"type\",\"path\":[\"argument\"],\"levels\":[]}" "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"CertificateWordRegistrationTemplates\",\"certificateWordRealization\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"
