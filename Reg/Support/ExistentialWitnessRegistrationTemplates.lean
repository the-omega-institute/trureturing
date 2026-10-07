import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates
open LeanInformationAudit
noncomputable def _root_.Reg.Support.ExistentialWitnessRegistrationTemplates.enrollment_1 : LeanInformationAudit.Contract.TemplateEnrollment.{2, 0} (@_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessRealization) := {
  name := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessRealization, version := 1, constructors := #[],
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency.types, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  bodyFact := `Reg.Support.ExistentialWitnessRegistrationTemplates.enrollment_1.bodyFact,
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates, declaration := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessRealization, part := .type, path := [], levels := [] },
    { owner := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates, declaration := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessRealization, part := .value, path := [], levels := [] }], facts := [] } }

end

noncomputable def Reg.Support.ExistentialWitnessRegistrationTemplates.enrollment_1.bodyFact : LeanInformationAudit.Contract.NodeFact :=
  compiled_exact% "{\"declaration\":[\"Reg\",\"Support\",\"ExistentialWitnessRegistrationTemplates\",\"enrollment_1\"],\"part\":\"type\",\"path\":[\"argument\"],\"levels\":[]}" "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"ExistentialWitnessRegistrationTemplates\",\"existentialWitnessRealization\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"
