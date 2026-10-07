import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration
open _root_.D5.S1.Words.HughesIterationDepthNoGap
open LeanInformationAudit
open RegistrationTemplates
noncomputable def _root_.Reg.Support.HughesIterationDepthNoGapRegistration.enrollment_1 : LeanInformationAudit.Contract.TemplateEnrollment.{1, 0} (@_root_.D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration.depthOriginTemplate) := {
  name := `D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration.depthOriginTemplate, version := 1, constructors := #[],
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  bodyFact := `Reg.Support.HughesIterationDepthNoGapRegistration.enrollment_1.bodyFact,
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration, declaration := `D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration.depthOriginTemplate, part := .type, path := [], levels := [] },
    { owner := `D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration, declaration := `D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration.depthOriginTemplate, part := .value, path := [], levels := [] }], facts := [] } }

end

noncomputable def Reg.Support.HughesIterationDepthNoGapRegistration.enrollment_1.bodyFact : LeanInformationAudit.Contract.NodeFact :=
  compiled_exact% "{\"declaration\":[\"Reg\",\"Support\",\"HughesIterationDepthNoGapRegistration\",\"enrollment_1\"],\"part\":\"type\",\"path\":[\"argument\"],\"levels\":[]}" "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"HughesIterationDepthNoGapRegistration\",\"depthOriginTemplate\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"
